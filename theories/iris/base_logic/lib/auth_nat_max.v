From heap_lang Require Import
  prelude.
From heap_lang.iris.algebra Require Import
  lib.auth_nat_max.
From heap_lang.iris.base_logic Require Export
  lib.base.
From heap_lang.iris Require Import
  diaframe.

Class AuthNatMaxG Σ := {
  #[local] auth_nat_max_G_inG :: inG Σ auth_nat_max_R ;
}.

Definition auth_nat_max_Σ := #[
  GFunctor auth_nat_max_R
].
#[global] Instance subG_auth_nat_max_Σ Σ :
  subG auth_nat_max_Σ Σ →
  AuthNatMaxG Σ.
Proof.
  solve_inG.
Qed.

Section auth_nat_max_G.
  Context `{auth_nat_max_G : !AuthNatMaxG Σ}.

  Implicit Types n m p : nat.

  Definition auth_nat_max_auth γ dq n :=
    own γ (auth_nat_max_auth dq n).
  Definition auth_nat_max_lb γ n :=
    own γ (auth_nat_max_lb n).

  #[global] Instance auth_nat_max_auth_timeless γ dq n :
    Timeless (auth_nat_max_auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max_auth_persistent γ n :
    Persistent (auth_nat_max_auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max_lb_timeless γ n :
    Timeless (auth_nat_max_lb γ n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max_lb_persistent γ n :
    Persistent (auth_nat_max_lb γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_max_auth_fractional γ n :
    Fractional (λ q, auth_nat_max_auth γ (DfracOwn q) n).
  Proof.
    intros ?*. rewrite -own_op -auth_nat_max_auth_dfrac_op //.
  Qed.
  #[global] Instance auth_nat_max_auth_as_fractional γ q n :
    AsFractional (auth_nat_max_auth γ (DfracOwn q) n) (λ q, auth_nat_max_auth γ (DfracOwn q) n) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_nat_max_alloc n :
    ⊢ |==>
      ∃ γ,
      auth_nat_max_auth γ (DfracOwn 1) n.
  Proof.
    iMod (own_alloc (auth_nat_max.auth_nat_max_auth (DfracOwn 1) n)) as "(% & ?)"; first apply auth_nat_max_auth_valid.
    iSteps.
  Qed.

  Lemma auth_nat_max_auth_valid γ dq a :
    auth_nat_max_auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "Hauth".
    iDestruct (own_valid with "[$]") as %?%auth_nat_max_auth_dfrac_valid.
    iSteps.
  Qed.
  Lemma auth_nat_max_auth_combine γ dq1 n1 dq2 n2 :
    auth_nat_max_auth γ dq1 n1 -∗
    auth_nat_max_auth γ dq2 n2 -∗
      auth_nat_max_auth γ (dq1 ⋅ dq2) n1 ∗
      ⌜n1 = n2⌝.
  Proof.
    iIntros "Hauth1 Hauth2". iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & <-)%auth_nat_max_auth_dfrac_op_valid.
    rewrite -auth_nat_max_auth_dfrac_op. iSteps.
  Qed.
  Lemma auth_nat_max_auth_valid_2 γ dq1 n1 dq2 n2 :
    auth_nat_max_auth γ dq1 n1 -∗
    auth_nat_max_auth γ dq2 n2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ n1 = n2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_nat_max_auth_combine with "Hauth1 Hauth2") as "(Hauth & %)".
    iDestruct (auth_nat_max_auth_valid with "Hauth") as %?.
    iSteps.
  Qed.
  Lemma auth_nat_max_auth_agree γ dq1 n1 dq2 n2 :
    auth_nat_max_auth γ dq1 n1 -∗
    auth_nat_max_auth γ dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_nat_max_auth_valid_2 with "Hauth1 Hauth2") as %?.
    iSteps.
  Qed.
  Lemma auth_nat_max_auth_dfrac_ne γ1 dq1 n1 γ2 dq2 n2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_nat_max_auth γ1 dq1 n1 -∗
    auth_nat_max_auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2 ->".
    iDestruct (auth_nat_max_auth_valid_2 with "Hauth1 Hauth2") as %?.
    naive_solver.
  Qed.
  Lemma auth_nat_max_auth_ne γ1 n1 γ2 dq2 n2 :
    auth_nat_max_auth γ1 (DfracOwn 1) n1 -∗
    auth_nat_max_auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_nat_max_auth_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_nat_max_auth_exclusive γ n1 n2 :
    auth_nat_max_auth γ (DfracOwn 1) n1 -∗
    auth_nat_max_auth γ (DfracOwn 1) n2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_nat_max_auth_valid_2 with "Hauth1 Hauth2") as %(? & _).
    iSmash.
  Qed.
  Lemma auth_nat_max_auth_persist γ dq n :
    auth_nat_max_auth γ dq n ⊢ |==>
    auth_nat_max_auth γ DfracDiscarded n.
  Proof.
    apply own_update, auth_nat_max_auth_persist.
  Qed.

  Lemma auth_nat_max_lb_0 γ :
    ⊢ |==>
      auth_nat_max_lb γ 0.
  Proof.
    apply own_unit.
  Qed.
  Lemma auth_nat_max_lb_get γ q n :
    auth_nat_max_auth γ q n ⊢
    auth_nat_max_lb γ n.
  Proof.
    apply own_mono, auth_nat_max_included.
  Qed.
  Lemma auth_nat_max_lb_le {γ n} n' :
    n' ≤ n →
    auth_nat_max_lb γ n ⊢
    auth_nat_max_lb γ n'.
  Proof.
    intros. apply own_mono, auth_nat_max_lb_mono. done.
  Qed.

  Lemma auth_nat_max_valid γ dq n m :
    auth_nat_max_auth γ dq n -∗
    auth_nat_max_lb γ m -∗
    ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (own_valid_2 with "Hauth1 Hauth2") as %?%auth_nat_max_both_dfrac_valid.
    iSteps.
  Qed.

  Lemma auth_nat_max_update {γ n} n' :
    n ≤ n' →
    auth_nat_max_auth γ (DfracOwn 1) n ⊢ |==>
    auth_nat_max_auth γ (DfracOwn 1) n'.
  Proof.
    iIntros "% Hauth".
    iMod (own_update with "Hauth"); first by apply auth_nat_max_auth_update.
    iSteps.
  Qed.
End auth_nat_max_G.

#[global] Opaque auth_nat_max_auth.
#[global] Opaque auth_nat_max_lb.
