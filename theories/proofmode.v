From iris.proofmode Require Export
  proofmode.

From diaframe Require Export
  proofmode_base.

From ml Require Export
  base.

(* FIXME: some goals are solved by [done] but not by [iSmash] *)
Tactic Notation "iSmash+" :=
  done || iSmash.
