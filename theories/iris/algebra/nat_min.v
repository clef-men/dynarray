From iris.algebra Require Import
  proofmode_classes.

From heap_lang Require Import
  prelude.
From heap_lang.iris.algebra Require Export
  base.

Record nat_min := {
  nat_min_car : nat ;
}.
Add Printing Constructor nat_min.

Canonical nat_min_O :=
  leibnizO nat_min.

Implicit Types n m : nat.
Implicit Types x y z : nat_min.

#[local] Instance nat_min_valid : Valid nat_min :=
  λ _,
    True.
#[local] Instance nat_min_validN : ValidN nat_min :=
  λ _ _,
    True.
#[local] Instance nat_min_pcore : PCore nat_min :=
  Some.
#[local] Instance nat_min_op : Op nat_min :=
  λ x1 x2,
    Build_nat_min (nat_min_car x1 `min` nat_min_car x2).

Lemma nat_min_op_eq n1 n2 :
  Build_nat_min n1 ⋅ Build_nat_min n2 = Build_nat_min (n1 `min` n2).
Proof.
  done.
Qed.

Lemma nat_min_included x1 x2 :
  x1 ≼ x2 ↔
  nat_min_car x2 ≤ nat_min_car x1.
Proof.
  split.
  - intros [y ->]. simpl. lia.
  - exists x2. rewrite /op /nat_min_op Nat.min_r; last lia. destruct x2. done.
Qed.

Lemma nat_min_ra_mixin :
  RAMixin nat_min.
Proof.
  apply ra_total_mixin; apply _ || eauto.
  - intros [] [] []. rewrite !nat_min_op_eq Nat.min_assoc //.
  - intros [] []. rewrite nat_min_op_eq Nat.min_comm //.
  - intros []. rewrite nat_min_op_eq Nat.min_id //.
Qed.
Canonical nat_min_R :=
  discreteR nat_min nat_min_ra_mixin.
#[global] Instance nat_min_cmra_discrete :
  CmraDiscrete nat_min_R.
Proof.
  apply discrete_cmra_discrete.
Qed.

#[global] Instance min_nat_core_id x :
  CoreId x.
Proof.
  constructor. done.
Qed.

Lemma nat_min_local_update x y x' :
  nat_min_car x' ≤ nat_min_car x →
  (x, y) ~l~> (x', x').
Proof.
  move: x y x' => [n] [m] [n'] /= ?.
  rewrite local_update_discrete. move=> [[p] |] _ /=; last done.
  rewrite !nat_min_op_eq => [= ?].
  split; first done. f_equal. lia.
Qed.

#[global] Instance nat_min_zero_l :
  LeftAbsorb (=) (Build_nat_min 0) (⋅).
Proof.
  done.
Qed.
#[global] Instance nat_min_zero_r :
  RightAbsorb (=) (Build_nat_min 0) (⋅).
Proof.
  intros [x]. rewrite nat_min_op_eq Nat.min_0_r //.
Qed.

#[global] Instance nat_min_op_idemp :
  IdemP (=@{nat_min}) (⋅).
Proof.
  intros []. rewrite nat_min_op_eq. f_equal. lia.
Qed.

#[global] Instance nat_min_is_op n1 n2 :
  IsOp (Build_nat_min (n1 `min` n2)) (Build_nat_min n1) (Build_nat_min n2).
Proof.
  done.
Qed.
