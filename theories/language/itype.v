From ml Require Import
  prelude.
From ml.language Require Export
  base.

Class iType (PROP : bi) (τ : val → PROP) :=
  itype v :> Persistent (τ v).

Section basic_types.
  Context {PROP : bi}.

  Implicit Types v : val.

  Definition int_type v : PROP :=
    ∃ i, ⌜v = LitV (LitInt i)⌝.
  #[global] Instance int_type_itype :
    iType _ int_type.
  Proof.
    intros ?. apply _.
  Qed.

  Definition nat_type v : PROP :=
    ∃ i, ⌜v = LitV (LitInt (Z.of_nat i))⌝.
  #[global] Instance nat_type_itype :
    iType _ nat_type.
  Proof.
    intros ?. apply _.
  Qed.

  Definition bool_type v : PROP :=
    ∃ b, ⌜v = LitV (LitBool b)⌝.
  #[global] Instance bool_type_itype :
    iType _ bool_type.
  Proof.
    intros ?. apply _.
  Qed.

  Definition unit_type v : PROP :=
    ⌜v = LitV LitUnit⌝.
  #[global] Instance unit_type_itype :
    iType _ unit_type.
  Proof.
    intros ?. apply _.
  Qed.
End basic_types.

Section other_types.
  Context `{!heapGS Σ}.

  Implicit Types v fn : val.

  Definition function_type τ1 `{!iType _ τ1} τ2 `{!iType _ τ2} fn : iProp Σ :=
    □ (∀ v, τ1 v -∗ WP App (Val fn) (Val v) {{ τ2 }}).
  #[global] Instance function_type_itype τ1 `{!iType _ τ1} τ2 `{!iType _ τ2} :
    iType _ (function_type τ1 τ2).
  Proof.
    intros ?. apply _.
  Qed.
End other_types.
