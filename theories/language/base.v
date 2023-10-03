From iris.bi Require Import
  lib.fractional.
From iris.heap_lang Require Export
  lang
  primitive_laws.
From iris.proofmode Require Import
  proofmode.

From ml Require Import
  prelude.

Lemma mapsto_dfrac_relax `{heapGS Σ} dq l v :
  ✓ dq →
  l ↦ v ==∗
  l ↦{dq} v.
Proof.
  iIntros "%Hdq H↦". destruct dq as [q1 | | q1].
  - destruct (decide (q1 < 1)%Qp) as [Hq1 | Hq1].
    + apply Qp.lt_sum in Hq1 as (q2 & ->).
      iDestruct (fractional_split with "H↦") as "(H↦1 & _)". done.
    + apply dfrac_valid_own, Qp.le_lteq in Hdq as [| ->]; done.
  - iApply (mapsto_persist with "H↦").
  - apply Qp.lt_sum in Hdq as (q2 & ->).
    iDestruct (fractional_split with "H↦") as "(H↦1 & H↦2)".
    iMod (mapsto_persist with "H↦2") as "H↦2".
    iDestruct (mapsto_combine with "H↦1 H↦2") as "($ & _)". done.
Qed.
