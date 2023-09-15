From stdpp Require Import
  strings.

From iris.proofmode Require Import
  string_ident.

From ml.prelude Require Export
  base.

Class TacticFlag (name : string) := {
  tactic_flag : bool ;
}.
#[global] Arguments tactic_flag _ {_} : assert.

Ltac tactic_flag_get name :=
  eval simpl in (tactic_flag name).

Ltac tactic_flag_set name opt :=
  string_to_ident_cps name ltac:(fun id =>
    try clear id;
    lazymatch tactic_flag_get name with
    | opt =>
        idtac
    | _ =>
        pose (id := {| tactic_flag := opt |} : TacticFlag name);
        move id at top
    end
  ).
Ltac tactic_flag_set_in name opt tac :=
  let old_opt := tactic_flag_get name in
  tactic_flag_set name opt;
  tac;
  tactic_flag_set name old_opt.

Ltac tactic_flag_enable name :=
  tactic_flag_set name true.
Ltac tactic_flag_enable_in name tac :=
  tactic_flag_set_in name true tac.

Ltac tactic_flag_disable name :=
  tactic_flag_set name false.
Ltac tactic_flag_disable_in name tac :=
  tactic_flag_set_in name false tac.
