From ml Require Import
  prelude.
From ml.language Require Import
  notations
  proofmode.
From ml.std Require Export
  base.

Section heapGS.
  Context `{!heapGS Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition reference_type t : iProp Σ :=
    ∃ (l : loc),
    ⌜t = #l⌝ ∗
    inv nroot (
      ∃ w,
      l ↦ w ∗ τ w
    ).
  #[global] Instance reference_type_itype :
    iType _ reference_type.
  Proof.
    intros ?. apply _.
  Qed.

  Lemma reference_make_spec_type v :
    {{{
      τ v
    }}}
      ref v
    {{{ t,
      RET t; reference_type t
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma reference_get_spec_type t :
    {{{
      reference_type t
    }}}
      !t
    {{{ v,
      RET v; τ v
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma reference_set_spec_type t v :
    {{{
      reference_type t ∗
      τ v
    }}}
      t <- v
    {{{
      RET #(); True
    }}}.
  Proof.
    iSmash.
  Qed.
End heapGS.

#[global] Opaque reference_type.
