From heap_lang Require Import
  prelude.
From heap_lang.common Require Import
  list.
From heap_lang.iris.bi Require Import
  big_op.
From heap_lang.language Require Import
  notations
  proofmode.
From heap_lang.std Require Export
  base.
From heap_lang.std Require Import
  diverge
  assume
  record2
  math
  reference
  opt
  array.

Section heap_GS.
  Context `{heap_GS : !heapGS Σ}.

  Implicit Types b : bool.
  Implicit Types i : nat.
  Implicit Types l r : loc.
  Implicit Types v t fn : val.
  Implicit Types vs : list val.

  Notation "t '.[size]'" :=
    t.[0]%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.[data]'" :=
    t.[1]%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.[size]'" :=
    t.[0]%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.[data]'" :=
    t.[1]%E
  ( at level 5
  ) : expr_scope.

  Definition safe_dynarray_create : val :=
    λ: <>,
      record2_make #0 (array_create #()).

  Definition safe_dynarray_make : val :=
    λ: "sz" "v",
      assume (#0 ≤ "sz") ;;
      record2_make "sz" (array_initi "sz" (λ: <>, &Some (ref "v"))).

  Definition safe_dynarray_initi : val :=
    λ: "sz" "fn",
      assume (#0 ≤ "sz") ;;
      record2_make "sz" (array_initi "sz" (λ: "i", &Some (ref ("fn" "i")))).

  Definition safe_dynarray_size : val :=
    λ: "t",
      !"t".[size].
  #[local] Definition safe_dynarray_data : val :=
    λ: "t",
      !"t".[data].
  Definition safe_dynarray_capacity : val :=
    λ: "t",
      array_size (safe_dynarray_data "t").

  #[local] Definition safe_dynarray_set_size : val :=
    λ: "t" "sz",
      "t".[size] <- "sz".
  #[local] Definition safe_dynarray_set_data : val :=
    λ: "t" "data",
      "t".[data] <- "data".

  Definition safe_dynarray_is_empty : val :=
    λ: "t",
      safe_dynarray_size "t" = #0.

  Definition safe_dynarray_get : val :=
    λ: "t" "i",
      match: array_get (safe_dynarray_data "t") "i" with
      | None =>
          diverge #()
      | Some "ref" =>
          !"ref"
      end.

  Definition safe_dynarray_set : val :=
    λ: "t" "i" "v",
      match: array_get (safe_dynarray_data "t") "i" with
      | None =>
          diverge #()
      | Some "ref" =>
          "ref" <- "v"
      end.

  #[local] Definition safe_dynarray_next_capacity : val :=
    λ: "n",
      maximum #8 (if: "n" ≤ #512 then #2 * "n" else "n" + "n" `quot` #2).
  Definition safe_dynarray_reserve : val :=
    λ: "t" "n",
      assume (#0 ≤ "n") ;;
      let: "data" := safe_dynarray_data "t" in
      let: "cap" := array_size "data" in
      if: "n" ≤ "cap" then (
        #()
      ) else (
        let: "new_cap" := maximum "n" (safe_dynarray_next_capacity "cap") in
        let: "new_data" := array_make "new_cap" &None in
        array_blit "data" #0 "new_data" #0 (safe_dynarray_size "t") ;;
        safe_dynarray_set_data "t" "new_data"
      ).
  Definition safe_dynarray_reserve_extra : val :=
    λ: "t" "n",
      assume (#0 ≤ "n") ;;
      safe_dynarray_reserve "t" (safe_dynarray_size "t" + "n").

  #[local] Definition safe_dynarray_try_push : val :=
    λ: "t" "slot",
      let: "sz" := safe_dynarray_size "t" in
      let: "data" := safe_dynarray_data "t" in
      if: array_size "data" ≤ "sz" then (
        #false
      ) else (
        safe_dynarray_set_size "t" (#1 + "sz") ;;
        array_unsafe_set "data" "sz" "slot" ;;
        #true
      ).
  #[local] Definition safe_dynarray_push_aux : val :=
    rec: "safe_dynarray_push_aux" "t" "slot" :=
      safe_dynarray_reserve_extra "t" #1 ;;
      if: safe_dynarray_try_push "t" "slot" then (
        #()
      ) else (
        "safe_dynarray_push_aux" "t" "slot"
      ).
  Definition safe_dynarray_push : val :=
    λ: "t" "v",
      let: "slot" := &Some (ref "v") in
      if: safe_dynarray_try_push "t" "slot" then (
        #()
      ) else (
        safe_dynarray_push_aux "t" "slot"
      ).

  Definition safe_dynarray_pop : val :=
    λ: "t",
      let: "sz" := safe_dynarray_size "t" in
      let: "data" := safe_dynarray_data "t" in
      assume ("sz" ≤ array_size "data") ;;
      assume (#0 < "sz") ;;
      let: "sz" := "sz" - #1 in
      match: array_unsafe_get "data" "sz" with
      | None =>
          diverge #()
      | Some "ref" =>
          array_unsafe_set "data" "sz" &None ;;
          safe_dynarray_set_size "t" "sz" ;;
          !"ref"
      end.

  Definition safe_dynarray_fit_capacity : val :=
    λ: "t",
      let: "sz" := safe_dynarray_size "t" in
      let: "data" := safe_dynarray_data "t" in
      if: array_size "data" = "sz" then (
        #()
      ) else (
        safe_dynarray_set_data "t" (array_shrink "data" "sz")
      ).

  Definition safe_dynarray_reset : val :=
    λ: "t",
      safe_dynarray_set_size "t" #0 ;;
      safe_dynarray_set_data "t" (array_create #()).

  Section safe_dynarray_model.
    #[local] Definition slot_model slot v : iProp Σ :=
      ∃ r,
      ⌜slot = &&Some #r⌝ ∗
      r ↦ v.
    Definition safe_dynarray_model t vs : iProp Σ :=
      ∃ l data slots extra,
      ⌜t = #l⌝ ∗
      l.[size] ↦ #(length vs) ∗
      l.[data] ↦ data ∗ array_model data (DfracOwn 1) (slots ++ replicate extra &&None) ∗
      [∗ list] slot; v ∈ slots; vs, slot_model slot v.

    #[global] Instance safe_dynarray_model_timeless t vs :
      Timeless (safe_dynarray_model t vs).
    Proof.
      apply _.
    Qed.
  End safe_dynarray_model.

  Lemma safe_dynarray_create_spec :
    {{{ True }}}
      safe_dynarray_create #()
    {{{ t,
      RET t;
      safe_dynarray_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_spec with "[//]"). iIntros "%data Hdata_model".
    wp_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)".
    iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iApply "HΦ". iExists l, data, [], 0. iSmash.
  Qed.

  Lemma safe_dynarray_make_spec sz v :
    (0 ≤ sz)%Z →
    {{{ True }}}
      safe_dynarray_make #sz v
    {{{ t,
      RET t;
      safe_dynarray_model t (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "_".
    wp_smart_apply (array_initi_spec_disentangled (λ _ slot, slot_model slot v)); [done | iSmash |]. iIntros "%data %slots (%Hslots & Hdata_model & Hslots)".
    wp_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)".
    iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iApply "HΦ". iExists l, data, slots, 0. iFrame. iSplit; first iSmash.
    rewrite replicate_length right_id. iFrame.
    iApply (big_sepL2_replicate_r_2 _ _ (λ _, slot_model) with "Hslots"). lia.
  Qed.

  Lemma safe_dynarray_initi_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      safe_dynarray_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      safe_dynarray_model t vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "_".
    pose Ψ' i slots := (
      ∃ vs,
      Ψ i vs ∗
      [∗ list] slot; v ∈ slots; vs, slot_model slot v
    )%I.
    wp_smart_apply (array_initi_spec Ψ' with "[HΨ]"); first done.
    { iSplitL "HΨ"; first iSmash. iIntros "!> %i %slots (%Hi1 & %Hi2) (%vs & HΨ & Hslots)".
      iDestruct (big_sepL2_length with "Hslots") as %Hslots.
      wp_smart_apply (wp_wand with "(Hfn [] HΨ)"); first iSmash. iIntros "%v HΨ".
      wp_alloc r as "Hr". wp_pures.
      iExists (vs ++ [v]). iFrame. iSmash.
    }
    iIntros "%data %slots (%Hslots & Hdata_model & (%vs & HΨ & Hslots))".
    wp_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)".
    iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iDestruct (big_sepL2_length with "Hslots") as %Hslots'.
    iApply "HΦ". iFrame. iSplit; first iSmash.
    iExists l, data, slots, 0. iFrame. iSplitR; first iSmash. iSplitL "Hsz"; first iSmash.
    rewrite right_id //.
  Qed.
  Lemma safe_dynarray_initi_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      safe_dynarray_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      safe_dynarray_model t vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (Z.to_nat sz - i), Ξ j
    )%I).
    wp_apply (safe_dynarray_initi_spec Ψ' with "[$HΨ Hfn]"); [done | | iSmash].
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (Z.to_nat sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma safe_dynarray_initi_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      safe_dynarray_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      safe_dynarray_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (safe_dynarray_initi_spec Ψ'); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSmash.
  Qed.
  Lemma safe_dynarray_initi_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      safe_dynarray_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      safe_dynarray_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (safe_dynarray_initi_spec' Ψ' with "[Hfn]"); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSmash.
  Qed.

  Lemma safe_dynarray_size_spec t vs :
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_size t
    {{{
      RET #(length vs);
      safe_dynarray_model t vs
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma safe_dynarray_capacity_spec t vs :
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_capacity t
    {{{ cap,
      RET #cap;
      ⌜length vs ≤ cap⌝ ∗
      safe_dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hmodel & Hslots) HΦ".
    wp_rec. rewrite /safe_dynarray_data. wp_load.
    wp_apply (array_size_spec with "Hmodel"). iIntros "Hmodel".
    rewrite app_length. iDestruct (big_sepL2_length with "Hslots") as %->.
    iSmash.
  Qed.

  Lemma safe_dynarray_is_empty_spec t vs :
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      safe_dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (safe_dynarray_size_spec with "Hmodel"). iIntros "Hmodel".
    wp_pures.
    destruct vs; iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma safe_dynarray_get_spec t vs (i : Z) v :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_get t #i
    {{{
      RET v;
      safe_dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Hi %Hvs_lookup %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    Z_to_nat i. rewrite Nat2Z.id in Hvs_lookup.
    clear Hi. pose proof Hvs_lookup as Hi%lookup_lt_Some.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    destruct (lookup_lt_is_Some_2 slots i) as (slot & Hslots_lookup); first lia.
    iDestruct (big_sepL2_lookup_acc with "Hslots") as "((%r & %Hr & Hr) & Hslots)"; [done.. | subst slot].
    wp_rec. rewrite /safe_dynarray_data. wp_load.
    wp_smart_apply (array_get_spec with "Hdata_model"); [lia | | done |].
    { rewrite Nat2Z.id lookup_app_l //. lia. }
    iSmash.
  Qed.

  Lemma safe_dynarray_set_spec t vs (i : Z) v :
    (0 ≤ i < length vs)%Z →
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_set t #i v
    {{{
      RET #();
      safe_dynarray_model t (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    feed pose proof (lookup_lookup_total vs i) as Hvs_lookup.
    { apply lookup_lt_is_Some_2. lia. }
    destruct (lookup_lt_is_Some_2 slots i) as (slot & Hslots_lookup); first lia.
    iDestruct (big_sepL2_insert_acc with "Hslots") as "((%r & %Hr & Hr) & Hslots)"; [done.. | subst slot].
    wp_rec. rewrite /safe_dynarray_data. wp_load.
    wp_smart_apply (array_get_spec with "Hdata_model"); [lia | | done |].
    { rewrite Nat2Z.id lookup_app_l //. lia. }
    iIntros "Hdata_model".
    wp_store.
    iDestruct ("Hslots" with "[Hr]") as "Hslots"; first iSmash.
    rewrite (list_insert_id slots) //.
    iApply "HΦ". iExists l, data, slots, extra. rewrite insert_length. iSmash.
  Qed.

  #[local] Lemma safe_dynarray_next_capacity_spec n :
    (0 ≤ n)%Z →
    {{{ True }}}
      safe_dynarray_next_capacity #n
    {{{ m,
      RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    Ltac Zify.zify_post_hook ::= Z.quot_rem_to_equations.
    iSmash.
  Qed.
  Lemma safe_dynarray_reserve_spec t vs n :
    (0 ≤ n)%Z →
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_reserve t #n
    {{{
      RET #();
      safe_dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    wp_rec. rewrite /safe_dynarray_data.
    wp_smart_apply assume_spec'. iIntros "_".
    wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model"). iIntros "Hdata_model".
    wp_pures.
    case_bool_decide; wp_pures; first iSmash.
    wp_smart_apply (safe_dynarray_next_capacity_spec with "[//]"); first lia. iIntros "%n' %Hn'".
    wp_apply maximum_spec.
    wp_smart_apply (array_make_spec with "[//]"); first lia. iIntros "%data' Hdata_model'".
    rewrite /safe_dynarray_size. wp_load.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    wp_smart_apply (array_blit_spec with "[$Hdata_model $Hdata_model']"); try lia.
    { rewrite app_length. lia. }
    { rewrite replicate_length. rewrite app_length in Hn'. lia. }
    iIntros "(Hdata_model & Hdata_model')".
    rewrite /safe_dynarray_set_data. wp_store.
    iApply "HΦ". iExists l, data', slots, _. iFrame. iSplitR; first iSmash.
    rewrite !Nat2Z.id drop_replicate take_app_alt //.
  Qed.
  Lemma safe_dynarray_reserve_extra_spec t vs n :
    (0 ≤ n)%Z →
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_reserve_extra t #n
    {{{
      RET #();
      safe_dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "_".
    wp_smart_apply (safe_dynarray_size_spec with "Hmodel"). iIntros "Hmodel".
    wp_smart_apply (safe_dynarray_reserve_spec with "Hmodel"); first lia.
    iSmash.
  Qed.

  #[local] Lemma safe_dynarray_try_push_spec t vs slot v :
    {{{
      safe_dynarray_model t vs ∗
      slot_model slot v
    }}}
      safe_dynarray_try_push t slot
    {{{ b,
      RET #b;
      if b then
        safe_dynarray_model t (vs ++ [v])
      else
        safe_dynarray_model t vs ∗
        slot_model slot v
    }}}.
  Proof.
    iIntros "%Φ ((%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) & Hslot) HΦ".
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    wp_rec. rewrite /safe_dynarray_size /safe_dynarray_data /safe_dynarray_set_size. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model"). iIntros "Hdata_model".
    wp_pures.
    case_bool_decide as Htest; wp_pures.
    { iApply "HΦ". iFrame. iSmash. }
    wp_store.
    wp_apply (array_unsafe_set_spec with "Hdata_model"); first lia. iIntros "Hdata_model".
    wp_pures.
    iApply "HΦ". iExists l, data, (slots ++ [slot]), (extra - 1). iFrame. iSplitR; first iSmash.
    rewrite app_length Z.add_1_l -Nat2Z.inj_succ Nat.add_comm /=. iFrame.
    rewrite Nat2Z.id -Hslots -(Nat.add_0_r (length slots)) insert_app_r.
    destruct extra.
    - rewrite app_length in Htest. naive_solver lia.
    - rewrite -(assoc (++)) /= Nat.sub_0_r. iSmash.
  Qed.
  #[local] Lemma safe_dynarray_push_aux_spec t vs slot v :
    {{{
      safe_dynarray_model t vs ∗
      slot_model slot v
    }}}
      safe_dynarray_push_aux t slot
    {{{
      RET #();
      safe_dynarray_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hslot) HΦ".
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply (safe_dynarray_reserve_extra_spec with "Hmodel"); first lia. iIntros "Hmodel".
    wp_smart_apply (safe_dynarray_try_push_spec with "[$Hmodel $Hslot]"). iIntros ([]); first iSmash. iIntros "(Hmodel & Hslot)".
    wp_smart_apply ("HLöb" with "Hmodel Hslot HΦ").
  Qed.
  Lemma safe_dynarray_push_spec t vs v :
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_push t v
    {{{
      RET #();
      safe_dynarray_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec. wp_alloc r as "Hr".
    wp_smart_apply (safe_dynarray_try_push_spec with "[$Hmodel Hr]"); first iSmash. iIntros ([]); first iSmash. iIntros "(Hmodel & Hslot)".
    wp_smart_apply (safe_dynarray_push_aux_spec with "[$Hmodel $Hslot]").
    iSmash.
  Qed.

  Lemma safe_dynarray_pop_spec {t vs} vs' v :
    vs = vs' ++ [v] →
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_pop t
    {{{
      RET v;
      safe_dynarray_model t vs'
    }}}.
  Proof.
    iIntros (->) "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    wp_rec. rewrite /safe_dynarray_size /safe_dynarray_data /safe_dynarray_set_size. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model"). iIntros "Hdata_model".
    do 2 (wp_smart_apply assume_spec'; iIntros "_").
    wp_pures.
    rewrite app_length Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; last lia.
    iDestruct (big_sepL2_length with "Hslots") as %Hslots. rewrite app_length /= in Hslots.
    destruct (rev_elim slots) as [-> | (slots_ & slot & ->)]; first (simpl in Hslots; lia).
    rewrite app_length Nat.add_cancel_r in Hslots. iEval (rewrite -Hslots).
    iDestruct (big_sepL2_snoc with "Hslots") as "(Hslots & (%r & -> & Hr))".
    wp_apply (array_unsafe_get_spec with "Hdata_model"); [lia | | done |].
    { rewrite Nat2Z.id lookup_app_l; last (rewrite app_length /=; lia).
      rewrite lookup_app_r // Nat.sub_diag //.
    }
    iIntros "Hdata_model".
    wp_smart_apply (array_unsafe_set_spec with "Hdata_model").
    { rewrite !app_length /=. lia. }
    iIntros "Hdata_model".
    rewrite -assoc Nat2Z.id insert_app_r_alt // Nat.sub_diag /=.
    wp_store. wp_load.
    iApply "HΦ". iExists l, data, slots_, (S extra).
    iSmash.
  Qed.

  Lemma safe_dynarray_fit_capacity_spec t vs :
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_fit_capacity t
    {{{
      RET #();
      safe_dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    wp_rec. rewrite /safe_dynarray_size /safe_dynarray_data /safe_dynarray_set_data. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model"). iIntros "Hdata_model".
    iDestruct (big_sepL2_length with "Hslots") as %Hslots.
    wp_pures.
    case_bool_decide; wp_pures; first iSmash.
    wp_apply (array_shrink_spec with "Hdata_model").
    { rewrite app_length. lia. }
    iIntros "%data' (_ & Hdata_model')".
    wp_store.
    iEval (rewrite -Hslots Nat2Z.id take_app) in "Hdata_model'".
    iApply "HΦ". iExists l, data', slots, 0.
    rewrite right_id. iSmash.
  Qed.

  Lemma safe_dynarray_reset_spec t vs :
    {{{
      safe_dynarray_model t vs
    }}}
      safe_dynarray_reset t
    {{{
      RET #();
      safe_dynarray_model t []
    }}}.
  Proof.
    iIntros "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & _ & _) HΦ".
    wp_rec. rewrite /safe_dynarray_set_size /safe_dynarray_set_data. wp_store.
    wp_apply (array_create_spec with "[//]"). iIntros "%data' Hdata_model'".
    wp_store.
    iSteps. iExists [], 0. iSmash.
  Qed.

  Context τ `{!iType (iPropI Σ) τ}.

  #[local] Definition slot_type :=
    opt_type (reference_type τ).
  Definition safe_dynarray_type t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    inv nroot (
      ∃ (sz : nat) cap data,
      l.[size] ↦ #sz ∗
      l.[data] ↦ data ∗ array_type slot_type cap data
    ).
  #[global] Instance safe_dynarray_type_itype :
    iType _ safe_dynarray_type.
  Proof.
    split. apply _.
  Qed.

  Lemma safe_dynarray_create_type :
    {{{ True }}}
      safe_dynarray_create #()
    {{{ t,
      RET t;
      safe_dynarray_type t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_type slot_type with "[//]"). iIntros "%data Hdata_type".
    iApply wp_fupd.
    wp_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)".
    iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iSmash.
  Qed.

  Lemma safe_dynarray_make_type (sz : Z) v :
    {{{
      τ v
    }}}
      safe_dynarray_make #sz v
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      safe_dynarray_type t
    }}}.
  Proof.
    iIntros "%Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "%Hsz".
    wp_smart_apply (array_initi_type slot_type); first iSmash. iIntros "%data (_ & Hdata_type)".
    iApply wp_fupd.
    wp_smart_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)".
    iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iSmash.
  Qed.

  Lemma safe_dynarray_size_type t :
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_size t
    {{{ (sz : nat),
      RET #sz; True
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma safe_dynarray_capacity_type t :
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_size t
    {{{ (cap : nat),
      RET #cap; True
    }}}.
  Proof.
    iSmash.
  Qed.

  #[local] Lemma safe_dynarray_data_type t :
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_data t
    {{{ cap data,
      RET data;
      array_type slot_type cap data
    }}}.
  Proof.
    iSmash.
  Qed.

  #[local] Lemma safe_dynarray_set_size_type t sz :
    (0 ≤ sz)%Z →
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_set_size t #sz
    {{{
      RET #(); True
    }}}.
  Proof.
    iSmash.
  Qed.

  #[local] Lemma safe_dynarray_set_data_type t cap data :
    {{{
      safe_dynarray_type t ∗
      array_type slot_type cap data
    }}}
      safe_dynarray_set_data t data
    {{{
      RET #(); True
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma safe_dynarray_is_empty_type t :
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_is_empty t
    {{{ b,
      RET #b; True
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma safe_dynarray_get_type t (i : Z) :
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_get t #i
    {{{ v,
      RET v;
      ⌜0 ≤ i⌝%Z ∗
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply (safe_dynarray_data_type with "Htype"). iIntros "%cap %data #Hdata_type".
    wp_apply (array_get_type with "Hdata_type"). iIntros "%slot (%Hi & #Hslot)".
    wp_apply (opt_type_match with "Hslot"). iSplit.
    - wp_apply wp_diverge.
    - iIntros "%r #Hr /=".
      wp_apply (reference_get_type with "Hr").
      iSmash.
  Qed.

  Lemma safe_dynarray_set_type t (i : Z) v :
    {{{
      safe_dynarray_type t ∗
      τ v
    }}}
      safe_dynarray_set t #i v
    {{{
      RET #();
      ⌜0 ≤ i⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (safe_dynarray_data_type with "Htype"). iIntros "%cap %data #Hdata_type".
    wp_apply (array_get_type with "Hdata_type"). iIntros "%slot (%Hi & #Hslot)".
    wp_apply (opt_type_match with "Hslot"). iSplit.
    - wp_apply wp_diverge.
    - iIntros "%r #Hr /=".
      wp_apply (reference_set_type with "[$Hr $Hv]").
      iSmash.
  Qed.

  Lemma safe_dynarray_reserve_type t n :
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_reserve t #n
    {{{
      RET #();
      ⌜0 ≤ n⌝%Z
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "%Hn".
    wp_smart_apply (safe_dynarray_data_type with "Htype"). iIntros "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type"). iIntros "_".
    wp_pures.
    case_bool_decide; wp_pures; first iSmash.
    wp_smart_apply (safe_dynarray_next_capacity_spec with "[//]"); first lia. iIntros "%n' %Hn'".
    wp_apply maximum_spec.
    wp_smart_apply (array_make_type slot_type); first iSmash. iIntros "%data' (_ & #Hdata_type')".
    wp_smart_apply safe_dynarray_size_type; first iSmash+. iIntros "%sz _".
    wp_smart_apply (array_blit_type slot_type); first iSmash. iIntros "_".
    wp_smart_apply (safe_dynarray_set_data_type with "[$Htype $Hdata_type']"). iIntros "_".
    iSmash.
  Qed.
  Lemma safe_dynarray_reserve_extra_type t n :
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_reserve_extra t #n
    {{{
      RET #();
      ⌜0 ≤ n⌝%Z
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "%Hn".
    wp_smart_apply (safe_dynarray_size_type with "Htype"). iIntros "%sz _".
    wp_smart_apply (safe_dynarray_reserve_type with "Htype").
    iSmash.
  Qed.

  #[local] Lemma safe_dynarray_try_push_type t slot :
    {{{
      safe_dynarray_type t ∗
      slot_type slot
    }}}
      safe_dynarray_try_push t slot
    {{{ b,
      RET #b; True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    wp_rec.
    wp_smart_apply (safe_dynarray_size_type with "Htype"). iIntros "%sz _".
    wp_smart_apply (safe_dynarray_data_type with "Htype"). iIntros "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type"). iIntros "_".
    wp_pures.
    case_bool_decide; wp_pures; first iSmash.
    wp_apply (safe_dynarray_set_size_type with "Htype"); first lia. iIntros "_".
    wp_smart_apply (array_unsafe_set_type with "[$Hdata_type $Hslot]"); first lia. iIntros "_".
    iSmash.
  Qed.
  #[local] Lemma safe_dynarray_push_aux_type t slot :
    {{{
      safe_dynarray_type t ∗
      slot_type slot
    }}}
      safe_dynarray_push_aux t slot
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply (safe_dynarray_reserve_extra_type with "Htype"). iIntros "_".
    wp_smart_apply (safe_dynarray_try_push_type with "[$Htype $Hslot]"). iIntros ([]) "_"; first iSmash.
    wp_smart_apply ("HLöb" with "HΦ").
  Qed.
  Lemma safe_dynarray_push_type t v :
    {{{
      safe_dynarray_type t ∗
      τ v
    }}}
      safe_dynarray_push t v
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec. wp_alloc r as "Hr".
    iAssert (|={⊤}=> slot_type (&&Some #r))%I with "[Hr]" as ">#Hslot"; first iSmash.
    wp_smart_apply (safe_dynarray_try_push_type with "[$Htype $Hslot]"). iIntros ([]) "_"; first iSmash.
    wp_smart_apply (safe_dynarray_push_aux_type with "[$Htype $Hslot]"). iIntros "_".
    iSmash.
  Qed.

  Lemma safe_dynarray_pop_type t :
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_pop t
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_apply (safe_dynarray_size_type with "Htype"). iIntros "%sz _".
    wp_smart_apply (safe_dynarray_data_type with "Htype"). iIntros "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type"). iIntros "_".
    wp_smart_apply assume_spec'. iIntros "%Hcap".
    wp_smart_apply assume_spec'. iIntros "%Hsz".
    wp_smart_apply (array_unsafe_get_type with "Hdata_type"); first lia. iIntros "%slot #Hslot".
    wp_apply (opt_type_match with "Hslot"). iSplit.
    - wp_apply wp_diverge.
    - iIntros "%r #Hr /=".
      wp_smart_apply (array_unsafe_set_type with "[$Hdata_type]"); [lia | iSmash |]. iIntros "_".
      wp_smart_apply (safe_dynarray_set_size_type with "Htype"); first lia. iIntros "_".
      wp_smart_apply (reference_get_type with "Hr").
      iSmash.
  Qed.

  Lemma safe_dynarray_fit_capacity_type t v :
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_fit_capacity t
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_apply (safe_dynarray_size_type with "Htype"). iIntros "%sz _".
    wp_smart_apply (safe_dynarray_data_type with "Htype"). iIntros "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type"). iIntros "_".
    wp_pures.
    case_decide; wp_pures; first iSmash.
    wp_apply (array_shrink_type with "Hdata_type"). iIntros "%t' (_ & #Hdata_type')".
    wp_apply (safe_dynarray_set_data_type with "[$Htype $Hdata_type']").
    iSmash.
  Qed.

  Lemma safe_dynarray_reset_type t v :
    {{{
      safe_dynarray_type t
    }}}
      safe_dynarray_reset t
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_apply (safe_dynarray_set_size_type with "Htype"); first done. iIntros "_".
    wp_smart_apply (array_create_type with "[//]"). iIntros "%data' #Hdata_type'".
    wp_apply (safe_dynarray_set_data_type with "[$Htype $Hdata_type']").
    iSmash.
  Qed.
End heap_GS.

#[global] Opaque safe_dynarray_create.
#[global] Opaque safe_dynarray_make.
#[global] Opaque safe_dynarray_initi.
#[global] Opaque safe_dynarray_size.
#[global] Opaque safe_dynarray_capacity.
#[global] Opaque safe_dynarray_is_empty.
#[global] Opaque safe_dynarray_get.
#[global] Opaque safe_dynarray_set.
#[global] Opaque safe_dynarray_reserve.
#[global] Opaque safe_dynarray_reserve_extra.
#[global] Opaque safe_dynarray_push.
#[global] Opaque safe_dynarray_pop.
#[global] Opaque safe_dynarray_fit_capacity.
#[global] Opaque safe_dynarray_reset.

#[global] Opaque safe_dynarray_model.
#[global] Opaque safe_dynarray_type.
