From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  notations.
From heap_lang.std Require Export
  base.

Definition lit_structural lit :=
  match lit with
  | LitInt _
  | LitBool _
  | LitUnit
  | LitLoc _ =>
      True
  | LitPoison
  | LitProphecy _ =>
      False
  end.
Fixpoint val_structural v :=
  match v with
  | LitV lit =>
      lit_structural lit
  | RecV _ _ _ =>
      False
  | PairV v1 v2 =>
      val_structural v1 ∧ val_structural v2
  | InjLV v =>
      val_structural v
  | InjRV v =>
      val_structural v
  end.

Parameter structural_equality : val.

Notation "e1 == e2" := (
  App (App (Val structural_equality) e1%E) e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 != e2" := (
  UnOp NegOp (App (App (Val structural_equality) e1%E) e2%E)
)(at level 70,
  no associativity
) : expr_scope.

Axiom wp_structural_equality : ∀ `{heap_GS : !heapGS Σ} v1 v2,
  val_structural v1 →
  val_structural v2 →
  ⊢ WP v1 == v2 {{ res, ⌜res = #(bool_decide (v1 = v2))⌝ }}.
