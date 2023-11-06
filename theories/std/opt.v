From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  notations
  proofmode.
From heap_lang.std Require Export
  base.

Notation "&None" := (
  InjL #()
)(only parsing
).
Notation "&&None" := (
  InjLV #()
)(only parsing
).
Notation "&Some" :=
  InjR
( only parsing
).
Notation "&&Some" :=
  InjRV
( only parsing
).

Notation "'match:' e0 'with' 'None' => e1 | 'Some' x => e2 'end'" := (
  Match e0 <>%binder e1 x%binder e2
)(e0, e1, x, e2 at level 200,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | 'None' => e1 | 'Some' x => e2 'end'" := (
  Match e0 <>%binder e1 x%binder e2
)(e0, e1, x, e2 at level 200,
  only parsing
) : expr_scope.

Section heap_GS.
  Context `{heap_GS : !heapGS Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition opt_type t : iProp Σ :=
      ⌜t = &&None⌝
    ∨ ∃ v, ⌜t = &&Some v⌝ ∗ τ v.
  #[global] Instance opt_type_itype :
    iType _ opt_type.
  Proof.
    split. apply _.
  Qed.

  Lemma opt_type_match t e1 x e2 Φ :
    opt_type t -∗
    ( WP e1 {{ Φ }} ∧
      ∀ v, τ v -∗ WP subst' x v e2 {{ Φ }}
    ) -∗
    WP match: t with None => e1 | Some x => e2 end {{ Φ }}.
  Proof.
    iIntros "[-> | (%v & -> & #Hv)] H";
      [rewrite bi.and_elim_l | rewrite bi.and_elim_r];
      iSmash.
  Qed.
End heap_GS.
