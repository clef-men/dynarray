From iris.heap_lang Require Export
  tactics.

From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  metatheory
  typeclass_instances
  notations.

Implicit Types v : val.

Lemma pure_exec_0 {Λ} ϕ (e : language.expr Λ) :
  PureExec ϕ 0 e e.
Proof.
  intros _. apply nsteps_O.
Qed.
Lemma pure_exec_add {Λ n} {ϕ : Prop} {e1 : language.expr Λ} ψ m e2 e3 :
  PureExec ψ m e1 e2 →
  (ϕ → ψ) →
  m ≤ n →
  PureExec ϕ (n - m) e2 e3 →
  PureExec ϕ n e1 e3.
Proof.
  intros Hpure1 Hψ Hle Hpure2 Hϕ.
  rewrite (Nat.le_add_sub m n) //. eapply nsteps_trans; naive_solver.
Qed.

#[local] Ltac solve_pure_exec' :=
  simpl;
  match goal with |- PureExec True ?n ?e1 ?e2 =>
    lazymatch n with
    | O =>
        apply pure_exec_0
    | S _ =>
        eapply pure_exec_add;
        [ reshape_expr e1 ltac:(fun K e1_foc =>
            apply (pure_exec_fill K _ _ e1_foc);
            apply _
          )
        | naive_solver
        | lia
        | idtac
        ]
    end
  end.
Ltac solve_pure_exec :=
  let H := fresh in
  pose (H := AsRecV_recv);
  repeat solve_pure_exec';
  simpl;
  clear H.

#[global] Instance pure_exec_subst_lam x1 v1 x2 v2 e :
  PureExec True 2
    ((subst' x1 v1 (λ: x2, e)) v2)
    (subst' x1 v1 (subst' x2 v2 e)).
Proof.
  destruct (decide (x1 = x2)) as [<- |].
  - rewrite subst_subst' subst_rec'; first naive_solver.
    solve_pure_exec.
  - rewrite subst_subst_ne' // subst_rec_ne'; [naive_solver.. |].
    solve_pure_exec.
Qed.
#[global] Instance pure_exec_subst2_lam x1 v1 x2 v2 x3 v3 e :
  PureExec True 2
    ((subst' x1 v1 (subst' x2 v2 (λ: x3, e))) v3)
    (subst' x1 v1 (subst' x2 v2 (subst' x3 v3 e))).
Proof.
  destruct (decide (x2 = x3)) as [<- |].
  - rewrite subst_subst' subst_rec'; first naive_solver.
    solve_pure_exec.
  - rewrite (subst_subst_ne' _ x2 x3) // subst_rec_ne'; [naive_solver.. |].
    destruct (decide (x1 = x3)) as [<- |].
    + rewrite subst_subst' subst_rec'; first naive_solver.
      solve_pure_exec.
    + rewrite (subst_subst_ne' _ x1 x3) // subst_rec_ne'; [naive_solver.. |].
      solve_pure_exec.
Qed.
