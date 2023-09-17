From ml Require Import
  prelude.
From ml.language Require Import
  notations
  proofmode.
From ml.std Require Export
  base.

Notation "&None" := (InjL #()).
Notation "&&None" := (InjLV #()).
Notation "&Some" := InjR.
Notation "&&Some" := InjRV.

Notation "'match:' e0 'with' 'None' => e1 | 'Some' x => e2 'end'" := (
    Match e0 <>%binder e1 x%binder e2
) (
  e0, e1, x, e2 at level 200,
  format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'None'  =>  '/  ' e1 ']'  '/' '[' |  'Some'  x  =>  '/  ' e2 ']'  '/' 'end' ']'"
) : expr_scope.
Notation "'match:' e0 'with' | 'None' => e1 | 'Some' x => e2 'end'" := (
    Match e0 <>%binder e1 x%binder e2
) (
  e0, e1, x, e2 at level 200,
  format "'[hv' 'match:'  e0  'with'  '/' '[' |  'None'  =>  '/  ' e1 ']'  '/' '[' |  'Some'  x  =>  '/  ' e2 ']'  '/' 'end' ']'"
) : expr_scope.

Section heapGS.
  Context `{!heapGS Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition opt_type t : iProp Σ :=
      ⌜t = &&None⌝
    ∨ ∃ v, ⌜t = &&Some v⌝ ∗ τ v.
  #[global] Instance opt_type_itype :
    iType _ opt_type.
  Proof.
    intros ?. apply _.
  Qed.
End heapGS.
