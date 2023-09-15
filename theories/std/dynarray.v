From ml Require Import
  prelude.
From ml.language Require Import
  notations
proofmode.
From ml.std Require Export
  base.
From ml.std Require Import
  record2
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

  Context τ `{!iType (iPropI Σ) τ}.

  #[local] Definition slot_type :=
    opt_type (reference_type τ).

  Definition dynarray_type t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    inv nroot (
      ∃ (sz : nat) data,
      l.[size] ↦ #sz ∗
      l.[data] ↦ data ∗ array_type slot_type data
    ).
  #[global] Instance dynarray_type_itype :
    iType _ dynarray_type.
  Proof.
    intros ?. apply _.
  Qed.

  Lemma dynarray_create_spec_type :
    {{{ True }}}
      dynarray_create #()
    {{{ t,
      RET t; dynarray_type t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_spec_type slot_type with "[//]"). iIntros "%data Hdata_type".
    iApply wp_fupd.
    wp_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)". iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iApply "HΦ". iExists l. iSplitR; first iSmash.
    iApply inv_alloc. iExists 0, data. iFrame.
  Qed.

  Lemma dynarray_make_spec_type sz v :
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
    case_bool_decide; first wp_smart_apply wp_diverge.
    Z_to_nat sz_ as sz.
    wp_smart_apply (array_init_spec_type slot_type); first iSmash. iIntros "%data Hdata_type".
    iApply wp_fupd.
    wp_smart_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & _)". iDestruct (record2_model_eq_1 with "Hl") as "(Hsz & Hdata)".
    iApply "HΦ". iExists l. iSplitR; first iSmash.
    iApply inv_alloc. iExists sz, data. iFrame.
  Qed.

  Lemma dynarray_get_spec_type t (i : val) :
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
    wp_bind (!_)%E. iInv "Hinv" as "(%sz & %data & >Hsz & >Hdata & #Hdata_type)".
    wp_load.
    iModIntro. iSplitR "HΦ".
    { iExists sz, data. iFrame "#∗". }
    wp_apply (array_get_spec_type with "[$Hdata_type]"); first iSmash. iIntros "%v [-> | (%ref & -> & #Href)]".
    - wp_smart_apply wp_diverge.
    - wp_smart_apply (reference_get_spec_type with "Href"). iSmash.
  Qed.

  Lemma dynarray_set_spec_type t (i : val) v :
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
    wp_bind (!_)%E. iInv "Hinv" as "(%sz & %data & >Hsz & >Hdata & #Hdata_type)".
    wp_load.
    iModIntro. iSplitR "HΦ".
    { iExists sz, data. iFrame "#∗". }
    wp_apply (array_get_spec_type with "[$Hdata_type]"); first iSmash. iIntros "%w [-> | (%ref & -> & #Href)]".
    - wp_smart_apply wp_diverge.
    - wp_smart_apply (reference_set_spec_type with "[$Href $Hv]"). iSmash.
  Qed.
End heapGS.

#[global] Opaque dynarray_create.
#[global] Opaque dynarray_make.
#[global] Opaque dynarray_get.
#[global] Opaque dynarray_set.
