From heap_lang Require Import
  prelude.
From heap_lang.iris.base_logic Require Export
  lib.base.
From heap_lang.iris.base_logic Require Import
  lib.ghost_var.
From heap_lang.iris Require Import
  proofmode.

Section support.
  Context (A : Type).

  Implicit Types a : A.

  Class OneshotG Σ := {
    #[local] oneshot_G :: GhostVarG Σ (A + A) ;
  }.

  Definition oneshot_Σ := #[
    ghost_var_Σ (A + A)
  ].
  #[global] Instance subG_oneshot_Σ Σ :
    subG oneshot_Σ Σ →
    OneshotG Σ.
  Proof.
    solve_inG.
  Qed.

  Section oneshot_G.
    Context `{oneshot_G : !OneshotG Σ}.

    Definition oneshot_pending γ dq a :=
      ghost_var γ dq (inl a).
    Definition oneshot_shot γ a :=
      ghost_var γ DfracDiscarded (inr a).

    #[global] Instance oneshot_pending_timeless γ dq a :
      Timeless (oneshot_pending γ dq a).
    Proof.
      apply _.
    Qed.
    #[global] Instance oneshot_shot_timeless γ a :
      Timeless (oneshot_shot γ a).
    Proof.
      apply _.
    Qed.
    #[global] Instance oneshot_shot_persistent γ a :
      Persistent (oneshot_shot γ a).
    Proof.
      apply _.
    Qed.

    #[global] Instance oneshot_pending_fractional γ a :
      Fractional (λ q, oneshot_pending γ (DfracOwn q) a).
    Proof.
      apply _.
    Qed.
    #[global] Instance oneshot_pending_as_fractional γ q a :
      AsFractional (oneshot_pending γ (DfracOwn q) a) (λ q, oneshot_pending γ (DfracOwn q) a) q.
    Proof.
      apply _.
    Qed.

    Lemma oneshot_alloc a :
      ⊢ |==>
        ∃ γ,
        oneshot_pending γ (DfracOwn 1) a.
    Proof.
      apply ghost_var_alloc.
    Qed.

    Lemma oneshot_pending_valid γ dq a :
      oneshot_pending γ dq a ⊢
      ⌜✓ dq⌝.
    Proof.
      apply ghost_var_valid.
    Qed.
    Lemma oneshot_pending_combine γ dq1 a1 dq2 a2 :
      oneshot_pending γ dq1 a1 -∗
      oneshot_pending γ dq2 a2 -∗
        oneshot_pending γ (dq1 ⋅ dq2) a1 ∗
        ⌜a1 = a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (ghost_var_combine with "H1 H2") as "($ & %Heq)". injection Heq as <-.
      iSteps.
    Qed.
    Lemma oneshot_pending_valid_2 γ dq1 a1 dq2 a2 :
      oneshot_pending γ dq1 a1 -∗
      oneshot_pending γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ a1 = a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (oneshot_pending_combine with "H1 H2") as "(H & <-)".
      iDestruct (oneshot_pending_valid with "H") as %?.
      iSteps.
    Qed.
    Lemma oneshot_pending_agree γ dq1 a1 dq2 a2 :
      oneshot_pending γ dq1 a1 -∗
      oneshot_pending γ dq2 a2 -∗
      ⌜a1 = a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (oneshot_pending_valid_2 with "H1 H2") as "(_ & $)".
    Qed.
    Lemma oneshot_pending_dfrac_ne γ1 dq1 a1 γ2 dq2 a2 :
      ¬ ✓ (dq1 ⋅ dq2) →
      oneshot_pending γ1 dq1 a1 -∗
      oneshot_pending γ2 dq2 a2 -∗
      ⌜γ1 ≠ γ2⌝.
    Proof.
      apply ghost_var_dfrac_ne.
    Qed.
    Lemma oneshot_pending_ne γ1 a1 γ2 dq2 a2 :
      oneshot_pending γ1 (DfracOwn 1) a1 -∗
      oneshot_pending γ2 dq2 a2 -∗
      ⌜γ1 ≠ γ2⌝.
    Proof.
      apply ghost_var_ne.
    Qed.
    Lemma oneshot_pending_exclusive γ a1 a2 :
      oneshot_pending γ (DfracOwn 1) a1 -∗
      oneshot_pending γ (DfracOwn 1) a2 -∗
      False.
    Proof.
      apply ghost_var_exclusive.
    Qed.
    Lemma oneshot_pending_persist γ dq a :
      oneshot_pending γ dq a ⊢ |==>
      oneshot_pending γ DfracDiscarded a.
    Proof.
      apply ghost_var_persist.
    Qed.

    Lemma oneshot_pending_shot γ dq a1 a2 :
      oneshot_pending γ dq a1 -∗
      oneshot_shot γ a2 -∗
      False.
    Proof.
      iIntros "Hpending Hshot".
      iDestruct (ghost_var_valid_2 with "Hpending Hshot") as %(_ & [=]).
    Qed.

    Lemma oneshot_update_pending γ a a' :
      oneshot_pending γ (DfracOwn 1) a ⊢ |==>
      oneshot_pending γ (DfracOwn 1) a'.
    Proof.
      apply ghost_var_update.
    Qed.
    Lemma oneshot_update_shot γ a a' :
      oneshot_pending γ (DfracOwn 1) a ⊢ |==>
      oneshot_shot γ a'.
    Proof.
      iIntros "Hpending".
      iMod (ghost_var_update with "Hpending") as "Hshot".
      iApply (ghost_var_persist with "Hshot").
    Qed.
  End oneshot_G.
End support.

#[global] Opaque oneshot_pending.
#[global] Opaque oneshot_shot.
