From ml Require Import
  prelude.
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

  Implicit Types i : nat.
  Implicit Types l : loc.
  Implicit Types v t : val.
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

  Definition dynarray_size : val :=
    λ: "t",
      !"t".[size].

  Definition dynarray_get : val :=
    λ: "t" "i",
      match: array_get !"t".[data] "i" with
      | None =>
          diverge #()
      | Some "ref" =>
          !"ref"
      end.

  Definition dynarray_set : val :=
    λ: "t" "i" "v",
      match: array_get !"t".[data] "i" with
      | None =>
          diverge #()
      | Some "ref" =>
          "ref" <- "v"
      end.

  #[local] Definition dynarray_next_capacity : val :=
    λ: "n",
      maximum #8 (if: "n" ≤ #512 then #2 * "n" else "n" + "n" `quot` #2).
  Definition dynarray_reserve : val :=
    λ: "t" "cap",
      let: "data" := !"t".[data] in
      let: "cur_cap" := array_size "data" in
      if: "cap" ≤ "cur_cap" then (
        #()
      ) else (
        if: "cap" < #0 then (
          diverge #()
        ) else (
          let: "new_cap" := maximum "cap" (dynarray_next_capacity "cur_cap") in
          let: "new_data" := array_make "new_cap" &None in
          array_blit "data" #0 "new_data" #0 (dynarray_size "t") ;;
          "t".[data] <- "new_data"
        )
      ).
  Definition dynarray_reserve_extra : val :=
    λ: "t" "n",
      dynarray_reserve "t" (dynarray_size "t" + "n").

  #[local] Definition dynarray_try_push : val :=
    λ: "t" "slot",
      let: "sz" := !"t".[size] in
      let: "data" := !"t".[data] in
      if: array_size "data" ≤ "sz" then (
        #false
      ) else (
        array_unsafe_set "data" "sz" "slot" ;;
        "t".[size] <- "sz" + #1 ;;
        #true
      ).
  #[local] Definition dynarray_push_aux : val :=
    rec: "dynaray_push_aux" "t" "slot" :=
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

  #[local] Definition dynarray_model_inner l (sz : nat) data vs : iProp Σ :=
    l.[size] ↦ #sz ∗
    l.[data] ↦ data ∗ array_model data (DfracOwn 1) vs.
  Definition dynarray_model t vs : iProp Σ :=
    ∃ l data ws,
    ⌜t = #l⌝ ∗
    dynarray_model_inner l (length vs) data (vs ++ ws).

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
    iIntros "%Φ ((%l & -> & #Hinv) & (%i_ & ->)) HΦ".
    wp_rec. wp_pures.
    wp_bind (!_)%E. iInv "Hinv" as "(%sz & %cap & %data & >Hsz & >Hdata & #Hdata_type)".
    wp_load.
    iModIntro. iSplitR "HΦ"; first iSmash.
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
    iIntros "%Φ ((%l & -> & #Hinv) & (%i_ & ->) & #Hv) HΦ".
    wp_rec. wp_pures.
    wp_bind (!_)%E. iInv "Hinv" as "(%sz & %cap & %data & >Hsz & >Hdata & #Hdata_type)".
    wp_load.
    iModIntro. iSplitR "HΦ"; first iSmash.
    wp_apply (array_get_type with "[$Hdata_type]"); first iSmash. iIntros "%w [-> | (%ref & -> & #Href)]".
    - wp_smart_apply wp_diverge.
    - wp_smart_apply (reference_set_type with "[$Href $Hv]"). iSmash.
  Qed.
End heapGS.

#[global] Opaque dynarray_create.
#[global] Opaque dynarray_make.
#[global] Opaque dynarray_size.
#[global] Opaque dynarray_get.
#[global] Opaque dynarray_set.
#[global] Opaque dynarray_reserve.
#[global] Opaque dynarray_reserve_extra.
#[global] Opaque dynarray_push.

#[global] Opaque dynarray_model.
#[global] Opaque dynarray_type.
