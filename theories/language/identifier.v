From heap_lang Require Import
  prelude.
From heap_lang Require Export
  language.
From heap_lang.language Require Import
  notations
  diaframe.

Definition identifier :=
  proph_id.
Canonical identifier_O :=
  leibnizO identifier.

Implicit Types id : identifier.

Definition LitIdentifier id :=
  LitProphecy id.
Coercion LitIdentifier : identifier >-> base_lit.

Notation NewId :=
  NewProph
( only parsing
).

Section heap_GS.
  Context `{heap_GS : !heapGS Σ}.

  Definition identifier_model id : iProp Σ :=
    ∃ prophs, proph id prophs.

  Lemma identifier_model_exclusive id :
    identifier_model id -∗
    identifier_model id -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma wp_new_id E :
    {{{ True }}}
      NewId @ E
    {{{ id,
      RET #id;
      identifier_model id
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wp_new_proph with "[//]").
    iSteps.
  Qed.
End heap_GS.

#[global] Opaque LitIdentifier.

#[global] Opaque identifier_model.
