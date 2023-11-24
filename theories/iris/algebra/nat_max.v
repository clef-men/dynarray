From iris.algebra Require Import
  proofmode_classes.

From heap_lang Require Import
  prelude.
From heap_lang.iris.algebra Require Export
  base.

Record nat_max := {
  nat_max_car : nat ;
}.
Add Printing Constructor nat_max.

Canonical nat_max_O :=
  leibnizO nat_max.

Implicit Types n m : nat.
Implicit Types x y z : nat_max.

#[local] Instance nat_max_valid : Valid nat_max :=
  λ _,
    True.
#[local] Instance nat_max_validN : ValidN nat_max :=
  λ _ _,
    True.
#[local] Instance nat_max_pcore : PCore nat_max :=
  Some.
#[local] Instance nat_max_op : Op nat_max :=
  λ x1 x2,
    Build_nat_max (nat_max_car x1 `max` nat_max_car x2).
#[local] Instance nat_max_unit : Unit nat_max :=
  Build_nat_max 0.

Lemma nat_max_op_eq n1 n2 :
  Build_nat_max n1 ⋅ Build_nat_max n2 = Build_nat_max (n1 `max` n2).
Proof.
  done.
Qed.

Lemma nat_max_included x1 x2 :
  x1 ≼ x2 ↔
  nat_max_car x1 ≤ nat_max_car x2.
Proof.
  split.
  - intros [y ->]. simpl. lia.
  - exists x2. rewrite /op /nat_max_op Nat.max_r; last lia. destruct x2. done.
Qed.

Lemma nat_max_ra_mixin :
  RAMixin nat_max.
Proof.
  apply ra_total_mixin; apply _ || eauto.
  - intros [] [] []. rewrite !nat_max_op_eq Nat.max_assoc //.
  - intros [] []. rewrite nat_max_op_eq Nat.max_comm //.
  - intros []. rewrite nat_max_op_eq Nat.max_id //.
Qed.
Canonical nat_max_R :=
  discreteR nat_max nat_max_ra_mixin.
#[global] Instance nat_max_cmra_discrete :
  CmraDiscrete nat_max_R.
Proof.
  apply discrete_cmra_discrete.
Qed.

Lemma nat_max_ucmra_mixin :
  UcmraMixin nat_max.
Proof.
  split; try apply _ || done. intros []. done.
Qed.
Canonical nat_max_UR :=
  Ucmra nat_max nat_max_ucmra_mixin.

#[global] Instance max_nat_core_id x :
  CoreId x.
Proof.
  constructor. done.
Qed.

Lemma nat_max_local_update x y x' :
  nat_max_car x ≤ nat_max_car x' →
  (x, y) ~l~> (x', x').
Proof.
  move: x y x' => [n] [m] [n'] /= ?.
  rewrite local_update_unital_discrete => [[p]] _.
  rewrite !nat_max_op_eq => [= ?].
  split; first done. f_equal. lia.
Qed.

#[global] Instance nat_max_op_idemp :
  IdemP (=@{nat_max}) (⋅).
Proof.
  intros []. rewrite nat_max_op_eq. f_equal. lia.
Qed.

#[global] Instance nat_max_is_op n1 n2 :
  IsOp (Build_nat_max (n1 `max` n2)) (Build_nat_max n1) (Build_nat_max n2).
Proof.
  done.
Qed.
