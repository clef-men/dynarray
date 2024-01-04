From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  tactics
  notations
  diaframe.
From heap_lang.std Require Export
  base.

Implicit Types v : val.

Definition opt_match : val :=
  λ: "t" "None" "Some",
    match: "t" with
      InjL <> =>
        "None" #()
    | InjR "x" =>
        "Some" "x"
    end.
Notation "'match:' e0 'with' | 'None' => e1 | 'Some' x => e2 'end'" :=
  (opt_match e0 (λ: <>, e1) (λ: x, e2))%E
( x at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match:  e0  with  '/' '[' |  None  =>  '/    ' e1 ']'  '/' '[' |  Some  x  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
Notation "'match:' e0 'with' 'None' => e1 | 'Some' x => e2 'end'" :=
  (opt_match e0 (λ: <>, e1) (λ: x, e2))%E
( x at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.
Notation "'match::' e0 'with' | 'None' => e1 | 'Some' x => e2 'end'" :=
  (opt_match e0 (λ: <>, e1)%V (λ: x, e2)%V)%E
( x at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match::  e0  with  '/' '[' |  None  =>  '/    ' e1 ']'  '/' '[' |  Some  x  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
Notation "'match::' e0 'with' 'None' => e1 | 'Some' x => e2 'end'" :=
  (opt_match e0 (λ: <>, e1)%V (λ: x, e2)%V)%E
( x at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.

Definition NoneV :=
  InjLV #().
Notation "'&&None'" :=
  NoneV.
#[global] Instance pure_opt_match_None e1 x e2 :
  PureExec True 9
    (match:: &&None with None => e1 | Some x => e2 end)
    e1.
Proof.
  solve_pure_exec.
Qed.

Definition opt_Some : val :=
  λ: "v", InjR "v".
Definition SomeV :=
  InjRV.
Notation "'&Some'" :=
  opt_Some.
Notation "'&&Some'" :=
  SomeV.
#[global] Instance opt_Some_inj :
  Inj (=) (=) &&Some.
Proof.
  rewrite /Inj. naive_solver.
Qed.
#[global] Instance pure_opt_Some v :
  PureExec True 2
    (&Some v)
    (&&Some v).
Proof.
  solve_pure_exec.
Qed.
#[global] Instance pure_opt_match_Some v e1 x e2 :
  PureExec True 9
    (match:: &&Some v with None => e1 | Some x => e2 end)
    (subst' x v e2).
Proof.
  solve_pure_exec.
Qed.

#[global] Opaque opt_match.
#[global] Opaque NoneV.
#[global] Opaque opt_Some.
#[global] Opaque SomeV.

Coercion opt_to_val o :=
  match o with
  | None =>
      &&None
  | Some v =>
      &&Some v
  end.

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
    WP match:: t with None => e1 | Some x => e2 end {{ Φ }}.
  Proof.
    iIntros "[-> | (%v & -> & #Hv)] H";
      [rewrite bi.and_elim_l | rewrite bi.and_elim_r];
      iSteps.
  Qed.
End heap_GS.
