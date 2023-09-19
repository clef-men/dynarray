From ml Require Import
  prelude.
From ml.bi Require Import
  big_op.
From ml.language Require Import
  notations
  proofmode.
From ml.std Require Export
  base.
From ml.std Require Import
  diverge
  record2
  math
  reference
  opt
  array.

Section heapGS.
  Context `{!heapGS Σ}.

  Implicit Types b : bool.
  Implicit Types i : nat.
  Implicit Types l r : loc.
  Implicit Types v t fn : val.
  Implicit Types vs : list val.

  Notation "t '.[size]'" := t.[0]%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.[data]'" := t.[1]%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.[size]'" := t.[0]%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.[data]'" := t.[1]%E
  ( at level 5
  ) : expr_scope.

  Definition dynarray_create : val :=
    λ: <>,
      record2_make #0 (array_create #()).

  Definition dynarray_make : val :=
    λ: "sz" "v",
      if: "sz" < #0 then (
        diverge #()
      ) else (
        record2_make "sz" (array_init "sz" (λ: <>, &Some (ref "v")))
      ).

  Definition dynarray_init : val :=
    λ: "sz" "fn",
      if: "sz" < #0 then (
        diverge #()
      ) else (
        record2_make "sz" (array_init "sz" (λ: "i", &Some (ref ("fn" "i"))))
      ).

  Definition dynarray_size : val :=
    λ: "t",
      !"t".[size].
  #[local] Definition dynarray_data : val :=
    λ: "t",
      !"t".[data].

  #[local] Definition dynarray_set_size : val :=
    λ: "t" "sz",
      "t".[size] <- "sz".
  #[local] Definition dynarray_set_data : val :=
    λ: "t" "data",
      "t".[data] <- "data".

  Definition dynarray_is_empty : val :=
    λ: "t",
      dynarray_size "t" = #0.

  Definition dynarray_get : val :=
    λ: "t" "i",
      match: array_get (dynarray_data "t") "i" with
      | None =>
          diverge #()
      | Some "ref" =>
          !"ref"
      end.

  Definition dynarray_set : val :=
    λ: "t" "i" "v",
      match: array_get (dynarray_data "t") "i" with
      | None =>
          diverge #()
      | Some "ref" =>
          "ref" <- "v"
      end.

  #[local] Definition dynarray_next_capacity : val :=
    λ: "n",
      maximum #8 (if: "n" ≤ #512 then #2 * "n" else "n" + "n" `quot` #2).
  Definition dynarray_reserve : val :=
    λ: "t" "n",
      let: "data" := dynarray_data "t" in
      let: "cap" := array_size "data" in
      if: "n" ≤ "cap" then (
        #()
      ) else (
        if: "n" < #0 then (
          diverge #()
        ) else (
          let: "new_cap" := maximum "n" (dynarray_next_capacity "cap") in
          let: "new_data" := array_make "new_cap" &None in
          array_blit "data" #0 "new_data" #0 (dynarray_size "t") ;;
          dynarray_set_data "t" "new_data"
        )
      ).
  Definition dynarray_reserve_extra : val :=
    λ: "t" "n",
      if: #0 ≤ "n" then (
        dynarray_reserve "t" (dynarray_size "t" + "n")
      ) else (
        #()
      ).

  #[local] Definition dynarray_try_push : val :=
    λ: "t" "slot",
      let: "sz" := dynarray_size "t" in
      let: "data" := dynarray_data "t" in
      if: array_size "data" ≤ "sz" then (
        #false
      ) else (
        array_unsafe_set "data" "sz" "slot" ;;
        dynarray_set_size "t" ("sz" + #1) ;;
        #true
      ).
  #[local] Definition dynarray_push_aux : val :=
    rec: "dynarray_push_aux" "t" "slot" :=
      dynarray_reserve_extra "t" #1 ;;
      if: dynarray_try_push "t" "slot" then (
        #()
      ) else (
        "dynarray_push_aux" "t" "slot"
      ).
  Definition dynarray_push : val :=
    λ: "t" "v",
      let: "slot" := &Some (ref "v") in
      if: dynarray_try_push "t" "slot" then (
        #()
      ) else (
        dynarray_push_aux "t" "slot"
      ).

  Section dynarray_model.
    #[local] Definition slot_model slot v : iProp Σ :=
      ∃ r,
      ⌜slot = &&Some #r⌝ ∗
      r ↦ v.
    Definition dynarray_model t vs : iProp Σ :=
      ∃ l data slots extra,
      ⌜t = #l⌝ ∗
      l.[size] ↦ #(length vs) ∗
      l.[data] ↦ data ∗ array_model data (DfracOwn 1) (slots ++ replicate extra &&None) ∗
      [∗list] slot; v ∈ slots; vs, slot_model slot v.

    #[global] Instance dynarray_model_timeless t vs :
      Timeless (dynarray_model t vs).
    Proof.
      apply _.
    Qed.
  End dynarray_model.

  Lemma dynarray_create_spec :
    {{{ True }}}
      dynarray_create #()
    {{{ t,
      RET t;
      dynarray_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_spec with "[//]"). iIntros "%data Hdata_model".
    wp_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)".
    iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iApply "HΦ". iExists l, data, [], 0. iSmash.
  Qed.

  Lemma dynarray_make_spec sz v :
    (0 ≤ sz)%Z →
    {{{ True }}}
      dynarray_make #sz v
    {{{ t,
      RET t;
      dynarray_model t (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp_rec. wp_pures.
    rewrite bool_decide_eq_false_2; last lia. wp_pures.
    wp_apply (array_init_spec_disentangled' (λ _ slot, slot_model slot v)); [done | iSmash |]. iIntros "%data %slots (%Hslots & Hdata_model & Hslots)".
    wp_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)".
    iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iApply "HΦ". iExists l, data, slots, 0. iFrame. iSplit; first iSmash.
    rewrite replicate_length right_id. iFrame.
    iApply (big_sepL2_replicate_r_2 _ _ (λ _, slot_model) with "Hslots"). lia.
  Qed.

  Lemma dynarray_init_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ [] ∗
      [∗ list] i ∈ seq 0 (Z.to_nat sz), ∀ vs_done,
        ⌜i = length vs_done⌝ -∗
        Ψ vs_done -∗
        WP fn #(i : nat) {{ v, Ψ (vs_done ++ [v]) }}
    }}}
      dynarray_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      dynarray_model t vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    wp_rec. wp_pures.
    rewrite bool_decide_eq_false_2; last lia. wp_pures.
    pose Ψ' slots := (
      ∃ vs,
      Ψ vs ∗
      [∗list] slot; v ∈ slots; vs, slot_model slot v
    )%I.
    wp_apply (array_init_spec Ψ' with "[HΨ Hfn]"); first done.
    { iSplitL "HΨ"; first iSmash.
      iApply (big_sepL_impl with "Hfn"). iIntros "!> %i %_i %Hi Hfn %slots -> (%vs & HΨ & Hslots)".
      iDestruct (big_sepL2_length with "Hslots") as %->.
      wp_smart_apply (wp_wand with "(Hfn [//] HΨ)"). iIntros "%v HΨ".
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
  Lemma dynarray_init_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ [] ∗
      ∀ i vs_done,
      {{{ ⌜i = length vs_done ∧ i < Z.to_nat sz⌝ ∗ Ψ vs_done }}}
        fn #i
      {{{ v, RET v; Ψ (vs_done ++ [v]) }}}
    }}}
      dynarray_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      dynarray_model t vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "% %Φ (HΨ & #Hfn) HΦ".
    wp_apply (dynarray_init_spec Ψ with "[$HΨ]"); try done.
    iApply big_sepL_intro. iIntros "!> %i %_i %H_i %vs_done % HΨ". apply lookup_seq in H_i as (-> & ?).
    iApply ("Hfn" with "[$HΨ]"); iSmash.
  Qed.
  Lemma dynarray_init_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #(i : nat) {{ Ψ i }}
    }}}
      dynarray_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      dynarray_model t vs ∗
      ([∗ list] i ↦ v ∈ vs, Ψ i v)
    }}}.
  Proof.
    iIntros "% %Φ Hfn HΦ".
    set (Ψ' vs := ([∗ list] i ↦ v ∈ vs, Ψ i v)%I).
    wp_apply (dynarray_init_spec Ψ' with "[Hfn]"); try done.
    iSplit; first rewrite /Ψ' //.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v % Hfn %vs_done -> HΨ'".
    iApply (wp_wand with "Hfn"). iIntros "%v HΨ". iFrame. iSplitL; last iSmash.
    rewrite right_id //.
  Qed.
  Lemma dynarray_init_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ∀ i,
      {{{ ⌜i < Z.to_nat sz⌝ }}}
        fn #i
      {{{ v, RET v; Ψ i v }}}
    }}}
      dynarray_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      dynarray_model t vs ∗
      ([∗ list] i ↦ v ∈ vs, Ψ i v)
    }}}.
  Proof.
    iIntros "% %Φ #Hfn HΦ".
    wp_apply dynarray_init_spec_disentangled; try done.
    iApply  big_sepL_intro. iIntros "!> %i %_i %Hlookup".
    apply lookup_seq in Hlookup as (-> & ?).
    iApply ("Hfn" with "[//]"). iSmash.
  Qed.

  Lemma dynarray_size_spec t vs :
    {{{
      dynarray_model t vs
    }}}
      dynarray_size t
    {{{
      RET #(length vs);
      dynarray_model t vs
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma dynarray_is_empty_spec t vs :
    {{{
      dynarray_model t vs
    }}}
      dynarray_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (dynarray_size_spec with "Hmodel"). iIntros "Hmodel".
    wp_pures.
    destruct vs; iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma dynarray_get_spec t vs (i : Z) v :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      dynarray_model t vs
    }}}
      dynarray_get t #i
    {{{
      RET v;
      dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Hi %Hvs_lookup %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    Z_to_nat i. rewrite Nat2Z.id in Hvs_lookup.
    clear Hi. pose proof Hvs_lookup as Hi%lookup_lt_Some.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    destruct (lookup_lt_is_Some_2 slots i) as (slot & Hslots_lookup); first lia.
    iDestruct (big_sepL2_lookup_acc with "Hslots") as "((%r & %Hr & Hr) & Hslots)"; [done.. | subst slot].
    wp_rec. rewrite /dynarray_data. wp_load.
    wp_smart_apply (array_get_spec with "Hdata_model"); first lia.
    { rewrite Nat2Z.id lookup_app_l //. lia. }
    iSmash.
  Qed.

  Lemma dynarray_set_spec t vs (i : Z) v :
    (0 ≤ i < length vs)%Z →
    {{{
      dynarray_model t vs
    }}}
      dynarray_set t #i v
    {{{
      RET #();
      dynarray_model t (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    feed pose proof (lookup_lookup_total vs i) as Hvs_lookup.
    { apply lookup_lt_is_Some_2. lia. }
    destruct (lookup_lt_is_Some_2 slots i) as (slot & Hslots_lookup); first lia.
    iDestruct (big_sepL2_insert_acc with "Hslots") as "((%r & %Hr & Hr) & Hslots)"; [done.. | subst slot].
    wp_rec. rewrite /dynarray_data. wp_load.
    wp_smart_apply (array_get_spec with "Hdata_model"); first lia.
    { rewrite Nat2Z.id lookup_app_l //. lia. }
    iIntros "Hdata_model".
    wp_store.
    iDestruct ("Hslots" with "[Hr]") as "Hslots"; first iSmash.
    rewrite (list_insert_id slots) //.
    iApply "HΦ". iExists l, data, slots, extra. rewrite insert_length. iSmash.
  Qed.

  #[local] Lemma dynarray_next_capacity_spec n :
    (0 ≤ n)%Z →
    {{{ True }}}
      dynarray_next_capacity #n
    {{{ m,
      RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    Ltac Zify.zify_post_hook ::= Z.quot_rem_to_equations.
    iSmash.
  Qed.
  Lemma dynarray_reserve_spec t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_model t vs
    }}}
      dynarray_reserve t #n
    {{{
      RET #();
      dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    wp_rec. rewrite /dynarray_data. wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model"). iIntros "Hdata_model".
    wp_pures.
    case_bool_decide; wp_pures; first iSmash.
    rewrite bool_decide_eq_false_2; last lia. wp_pures.
    wp_apply (dynarray_next_capacity_spec with "[//]"); first lia. iIntros "%n' %Hn'".
    wp_apply maximum_spec.
    wp_smart_apply (array_make_spec with "[//]"); first lia. iIntros "%data' Hdata_model'".
    rewrite /dynarray_size. wp_load.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    wp_smart_apply (array_blit_spec with "[$Hdata_model $Hdata_model']"); try lia.
    { rewrite app_length. lia. }
    { rewrite replicate_length. rewrite app_length in Hn'. lia. }
    iIntros "(Hdata_model & Hdata_model')".
    rewrite /dynarray_set_data. wp_store.
    iApply "HΦ". iExists l, data', slots, _. iFrame. iSplitR; first iSmash.
    rewrite !Nat2Z.id drop_replicate take_app_alt //.
  Qed.
  Lemma dynarray_reserve_extra_spec t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_model t vs
    }}}
      dynarray_reserve_extra t #n
    {{{
      RET #();
      dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ Hmodel HΦ".
    wp_rec. wp_pures.
    case_bool_decide; wp_pures; last iSmash+.
    wp_apply (dynarray_size_spec with "Hmodel"). iIntros "Hmodel".
    wp_smart_apply (dynarray_reserve_spec with "Hmodel"); first lia.
    iSmash.
  Qed.

  #[local] Lemma dynarray_try_push_spec t vs slot v :
    {{{
      dynarray_model t vs ∗
      slot_model slot v
    }}}
      dynarray_try_push t slot
    {{{ b,
      RET #b;
      if b then
        dynarray_model t (vs ++ [v])
      else
        dynarray_model t vs ∗
        slot_model slot v
    }}}.
  Proof.
    iIntros "%Φ ((%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) & Hslot) HΦ".
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    wp_rec. rewrite /dynarray_size /dynarray_data. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model"). iIntros "Hdata_model".
    wp_pures.
    case_bool_decide as Htest; wp_pures.
    { iApply "HΦ". iFrame. iSmash. }
    wp_apply (array_unsafe_set_spec with "Hdata_model"); first lia. iIntros "Hdata_model".
    rewrite /dynarray_set_size. wp_store.
    iApply "HΦ". iExists l, data, (slots ++ [slot]), (extra - 1). iFrame. iSplitR; first iSmash.
    rewrite app_length Z.add_1_r -Nat2Z.inj_succ Nat.add_comm /=. iFrame.
    rewrite Nat2Z.id -Hslots -(Nat.add_0_r (length slots)) insert_app_r.
    destruct extra.
    - rewrite app_length in Htest. naive_solver lia.
    - rewrite -(assoc (++)) /= Nat.sub_0_r. iSmash.
  Qed.
  #[local] Lemma dynarray_push_aux_spec t vs slot v :
    {{{
      dynarray_model t vs ∗
      slot_model slot v
    }}}
      dynarray_push_aux t slot
    {{{
      RET #();
      dynarray_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hslot) HΦ".
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply (dynarray_reserve_extra_spec with "Hmodel"); first lia. iIntros "Hmodel".
    wp_smart_apply (dynarray_try_push_spec with "[$Hmodel $Hslot]"). iIntros ([]); first iSmash. iIntros "(Hmodel & Hslot)".
    wp_smart_apply ("HLöb" with "Hmodel Hslot HΦ").
  Qed.
  Lemma dynarray_push_spec t vs v :
    {{{
      dynarray_model t vs
    }}}
      dynarray_push t v
    {{{
      RET #();
      dynarray_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec. wp_alloc r as "Hr".
    wp_smart_apply (dynarray_try_push_spec with "[$Hmodel Hr]"); first iSmash. iIntros ([]); first iSmash. iIntros "(Hmodel & Hslot)".
    wp_smart_apply (dynarray_push_aux_spec with "[$Hmodel $Hslot]").
    iSmash.
  Qed.

  Context τ `{!iType (iPropI Σ) τ}.

  #[local] Definition slot_type :=
    opt_type (reference_type τ).
  Definition dynarray_type t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    inv nroot (
      ∃ (sz : nat) cap data,
      l.[size] ↦ #sz ∗
      l.[data] ↦ data ∗ array_type slot_type cap data
    ).
  #[global] Instance dynarray_type_itype :
    iType _ dynarray_type.
  Proof.
    intros ?. apply _.
  Qed.

  Lemma dynarray_create_type :
    {{{ True }}}
      dynarray_create #()
    {{{ t,
      RET t; dynarray_type t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_type slot_type with "[//]"). iIntros "%data Hdata_type".
    iApply wp_fupd.
    wp_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)". iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iSmash.
  Qed.

  Lemma dynarray_make_type sz v :
    {{{
      int_type sz ∗
      τ v
    }}}
      dynarray_make sz v
    {{{ t,
      RET t; dynarray_type t
    }}}.
  Proof.
    iIntros "%Φ ((%sz_ & ->) & #Hv) HΦ".
    wp_rec. wp_pures.
    case_bool_decide; wp_pures; first wp_apply wp_diverge.
    Z_to_nat sz_ as sz.
    wp_apply (array_init_type slot_type); first iSmash. iIntros "%data Hdata_type".
    iApply wp_fupd.
    wp_smart_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)". iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iSmash.
  Qed.

  Lemma dynarray_size_type t :
    {{{
      dynarray_type t
    }}}
      dynarray_size t
    {{{ (sz : nat),
      RET #sz; True
    }}}.
  Proof.
    iSmash.
  Qed.

  #[local] Lemma dynarray_data_type t :
    {{{
      dynarray_type t
    }}}
      dynarray_data t
    {{{ cap data,
      RET data;
      array_type slot_type cap data
    }}}.
  Proof.
    iSmash.
  Qed.

  #[local] Lemma dynarray_set_size_type t sz :
    {{{
      dynarray_type t ∗
      nat_type sz
    }}}
      dynarray_set_size t sz
    {{{
      RET #(); True
    }}}.
  Proof.
    iSmash.
  Qed.

  #[local] Lemma dynarray_set_data_type t cap data :
    {{{
      dynarray_type t ∗
      array_type slot_type cap data
    }}}
      dynarray_set_data t data
    {{{
      RET #(); True
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma dynarray_is_empty_type t :
    {{{
      dynarray_type t
    }}}
      dynarray_is_empty t
    {{{ b,
      RET #b; True
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma dynarray_get_type t (i : val) :
    {{{
      dynarray_type t ∗
      int_type i
    }}}
      dynarray_get t i
    {{{ v,
      RET v; τ v
    }}}.
  Proof.
    iIntros "%Φ (#Htype & (%i_ & ->)) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_data_type with "Htype"). iIntros "%cap %data #Hdata_type".
    wp_apply (array_get_type with "[$Hdata_type]"); first iSmash. iIntros "%v [-> | (%ref & -> & #Href)]".
    - wp_smart_apply wp_diverge.
    - wp_smart_apply (reference_get_type with "Href"). iSmash.
  Qed.

  Lemma dynarray_set_type t (i : val) v :
    {{{
      dynarray_type t ∗
      int_type i ∗
      τ v
    }}}
      dynarray_set t i v
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & (%i_ & ->) & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_data_type with "Htype"). iIntros "%cap %data #Hdata_type".
    wp_apply (array_get_type with "[$Hdata_type]"); first iSmash. iIntros "%w [-> | (%ref & -> & #Href)]".
    - wp_smart_apply wp_diverge.
    - wp_smart_apply (reference_set_type with "[$Href $Hv]"). iSmash.
  Qed.

  Lemma dynarray_reserve_type t n :
    {{{
      dynarray_type t ∗
      int_type n
    }}}
      dynarray_reserve t n
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & (%n_ & ->)) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_data_type with "Htype"). iIntros "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type"). iIntros "_".
    wp_pures.
    case_bool_decide; wp_pures; first iSmash.
    case_bool_decide; wp_pures; first wp_apply wp_diverge.
    wp_apply (dynarray_next_capacity_spec with "[//]"); first lia. iIntros "%n' %Hn'".
    wp_apply maximum_spec.
    wp_smart_apply (array_make_type slot_type); first iSmash. iIntros "%data' #Hdata_type'".
    wp_smart_apply dynarray_size_type; first iSmash+. iIntros "%sz _".
    wp_smart_apply (array_blit_type slot_type); first iSmash. iIntros "_".
    wp_smart_apply (dynarray_set_data_type with "[$Htype $Hdata_type']"). iIntros "_".
    iSmash.
  Qed.
  Lemma dynarray_reserve_extra_type t n :
    {{{
      dynarray_type t ∗
      int_type n
    }}}
      dynarray_reserve_extra t n
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & (%n_ & ->)) HΦ".
    wp_rec. wp_pures.
    case_bool_decide; wp_pures; last iSmash.
    wp_apply (dynarray_size_type with "Htype"). iIntros "%sz _".
    wp_smart_apply (dynarray_reserve_type with "[$Htype]"); first iSmash.
    iSmash.
  Qed.

  #[local] Lemma dynarray_try_push_type t slot :
    {{{
      dynarray_type t ∗
      slot_type slot
    }}}
      dynarray_try_push t slot
    {{{ b,
      RET #b; True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_size_type with "Htype"). iIntros "%sz _".
    wp_smart_apply (dynarray_data_type with "Htype"). iIntros "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type"). iIntros "_".
    wp_pures.
    case_bool_decide; wp_pures; first iSmash.
    wp_apply (array_unsafe_set_type with "[$Hdata_type $Hslot]"); first lia. iIntros "_".
    wp_smart_apply (dynarray_set_size_type with "[$Htype]"); first iSmash. iIntros "_".
    iSmash.
  Qed.
  #[local] Lemma dynarray_push_aux_type t slot :
    {{{
      dynarray_type t ∗
      slot_type slot
    }}}
      dynarray_push_aux t slot
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply (dynarray_reserve_extra_type with "[$Htype]"); first iSmash. iIntros "_".
    wp_smart_apply (dynarray_try_push_type with "[$Htype $Hslot]"). iIntros ([]) "_"; first iSmash.
    wp_smart_apply ("HLöb" with "HΦ").
  Qed.
  Lemma dynarray_push_type t v :
    {{{
      dynarray_type t ∗
      τ v
    }}}
      dynarray_push t v
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec. wp_alloc r as "Hr".
    iAssert (|={⊤}=> slot_type (&&Some #r))%I with "[Hr]" as ">#Hslot"; first iSmash.
    wp_smart_apply (dynarray_try_push_type with "[$Htype $Hslot]"). iIntros ([]) "_"; first iSmash.
    wp_smart_apply (dynarray_push_aux_type with "[$Htype $Hslot]"). iIntros "_".
    iSmash.
  Qed.
End heapGS.

#[global] Opaque dynarray_create.
#[global] Opaque dynarray_make.
#[global] Opaque dynarray_init.
#[global] Opaque dynarray_size.
#[global] Opaque dynarray_is_empty.
#[global] Opaque dynarray_get.
#[global] Opaque dynarray_set.
#[global] Opaque dynarray_reserve.
#[global] Opaque dynarray_reserve_extra.
#[global] Opaque dynarray_push.

#[global] Opaque dynarray_model.
#[global] Opaque dynarray_type.
