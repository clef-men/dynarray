From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  notations
  proofmode.
From heap_lang.std Require Export
  base.

Section heap_GS.
  Context `{heap_GS : !heapGS Σ}.
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
    split. apply _.
  Qed.

  Lemma reference_make_type v :
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

  Lemma reference_get_type t :
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

  Lemma reference_set_type t v :
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
End heap_GS.
