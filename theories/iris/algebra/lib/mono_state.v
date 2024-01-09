From iris.algebra Require Import
  proofmode_classes.

From heap_lang Require Import
  prelude.
From heap_lang.iris.algebra Require Export
  base.
From heap_lang.iris.algebra Require Import
  auth
  mono.

Section sts.
  Context `(step : relation state).

  Implicit Types s t : state.

  Let state_O :=
    leibnizO state.
  #[local] Canonical state_O.

  Notation steps := (
    rtc step
  ).

  Definition mono_state :=
    auth (mra steps).
  Definition mono_state_R :=
    authR (mraUR steps).
  Definition mono_state_UR :=
    authUR (mraUR steps).

  Definition mono_state_auth dq s : mono_state_UR :=
    ●{dq} principal steps s ⋅ ◯ principal steps s.
  Definition mono_state_lb s : mono_state_UR :=
    ◯ principal steps s.

  #[global] Instance mono_state_auth_inj `{!AntiSymm (=) steps} :
    Inj2 (=) (=) (≡) mono_state_auth.
  Proof.
    rewrite /Inj2. setoid_rewrite auth_auth_frag_dfrac_op.
    intros * (-> & ->%(@inj _ _ (≡) _ _ _) & _). done.
  Qed.
  #[global] Instance mono_state_lb_inj `{!AntiSymm (=) steps} :
    Inj (=) (≡) mono_state_lb.
  Proof.
    intros s1 s2 ->%(inj auth_frag)%(@inj _ _ (≡) _ _ _). done.
  Qed.

  #[global] Instance mono_state_cmra_discrete :
    CmraDiscrete mono_state_R.
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_state_auth_core_id s :
    CoreId (mono_state_auth DfracDiscarded s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_state_lb_core_id s :
    CoreId (mono_state_lb s).
  Proof.
    apply _.
  Qed.

  Lemma mono_state_auth_dfrac_op dq1 dq2 s :
    mono_state_auth (dq1 ⋅ dq2) s ≡ mono_state_auth dq1 s ⋅ mono_state_auth dq2 s.
  Proof.
    rewrite /mono_state_auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)) -core_id_dup (comm _ (◯ _)) //.
  Qed.
  #[global] Instance mono_state_auth_dfrac_is_op dq dq1 dq2 s :
    IsOp dq dq1 dq2 →
    IsOp' (mono_state_auth dq s) (mono_state_auth dq1 s) (mono_state_auth dq2 s).
  Proof.
    rewrite /IsOp' /IsOp => ->. rewrite mono_state_auth_dfrac_op //.
  Qed.

  Lemma mono_state_lb_op s s' :
    steps s s' →
    mono_state_lb s' ≡ mono_state_lb s ⋅ mono_state_lb s'.
  Proof.
    intros. rewrite -auth_frag_op principal_R_op //.
  Qed.

  Lemma mono_state_auth_frag_op dq s :
    mono_state_auth dq s ≡ mono_state_auth dq s ⋅ mono_state_lb s.
  Proof.
    rewrite /mono_state_auth /mono_state_lb.
    rewrite -!assoc -auth_frag_op -core_id_dup //.
  Qed.

  Lemma mono_state_auth_dfrac_valid dq s :
    ✓ mono_state_auth dq s ↔
    ✓ dq.
  Proof.
    rewrite auth_both_dfrac_valid_discrete /=. naive_solver.
  Qed.
  Lemma mono_state_auth_valid s :
    ✓ mono_state_auth (DfracOwn 1) s.
  Proof.
    rewrite mono_state_auth_dfrac_valid //.
  Qed.

  Lemma mono_state_auth_dfrac_op_valid `{!AntiSymm (=) steps} dq1 s1 dq2 s2 :
    ✓ (mono_state_auth dq1 s1 ⋅ mono_state_auth dq2 s2) ↔
    ✓ (dq1 ⋅ dq2) ∧ s1 = s2.
  Proof.
    rewrite /mono_state_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move => /cmra_valid_op_l /auth_auth_dfrac_op_valid.
      split; last apply (inj (principal steps)); naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
      apply auth_both_dfrac_valid_discrete. done.
  Qed.
  Lemma mono_state_auth_op_valid `{!AntiSymm (=) steps} s1 s2 :
    ✓ (mono_state_auth (DfracOwn 1) s1 ⋅ mono_state_auth (DfracOwn 1) s2) ↔
    False.
  Proof.
    rewrite mono_state_auth_dfrac_op_valid. naive_solver.
  Qed.

  Lemma mono_state_both_dfrac_valid dq s t :
    ✓ (mono_state_auth dq s ⋅ mono_state_lb t) ↔
    ✓ dq ∧ steps t s.
  Proof.
    rewrite -assoc -auth_frag_op auth_both_dfrac_valid_discrete. split.
    - intros. split; first naive_solver.
      rewrite -principal_included. etrans; [apply @cmra_included_r | naive_solver].
    - intros. rewrite (comm op) principal_R_op; naive_solver.
  Qed.
  Lemma mono_state_both_valid s t :
    ✓ (mono_state_auth (DfracOwn 1) s ⋅ mono_state_lb t) ↔
    steps t s.
  Proof.
    rewrite mono_state_both_dfrac_valid dfrac_valid_own. naive_solver.
  Qed.

  Lemma mono_state_lb_mono s1 s2 :
    steps s1 s2 →
    mono_state_lb s1 ≼ mono_state_lb s2.
  Proof.
    intros. apply auth_frag_mono. rewrite principal_included //.
  Qed.

  Lemma mono_state_auth_dfrac_included `{!AntiSymm (=) steps} dq1 s1 dq2 s2 :
    mono_state_auth dq1 s1 ≼ mono_state_auth dq2 s2 ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ s1 = s2.
  Proof.
    rewrite auth_both_dfrac_included principal_included. split; last naive_solver.
    intros (? & ->%(@inj _ _ (≡) _ _ _) & ?). done.
  Qed.
  Lemma mono_state_auth_included `{!AntiSymm (=) steps} s1 s2 :
    mono_state_auth (DfracOwn 1) s1 ≼ mono_state_auth (DfracOwn 1) s2 ↔
    s1 = s2.
  Proof.
    rewrite mono_state_auth_dfrac_included. naive_solver.
  Qed.

  Lemma mono_state_lb_included s1 dq s2 :
    mono_state_lb s1 ≼ mono_state_auth dq s2 ↔
    steps s1 s2.
  Proof.
    rewrite auth_frag_included principal_included //.
  Qed.
  Lemma mono_state_lb_included' s dq :
    mono_state_lb s ≼ mono_state_auth dq s.
  Proof.
    rewrite mono_state_lb_included //.
  Qed.

  Lemma mono_state_auth_persist dq s :
    mono_state_auth dq s ~~> mono_state_auth DfracDiscarded s.
  Proof.
    eapply cmra_update_op_proper; last done.
    eapply auth_update_auth_persist.
  Qed.
  Lemma mono_state_auth_update {s} s' :
    steps s s' →
    mono_state_auth (DfracOwn 1) s ~~> mono_state_auth (DfracOwn 1) s'.
  Proof.
    intros. apply auth_update, mra_local_update_grow. done.
  Qed.

  Lemma mono_state_auth_local_update s s' :
    steps s s' →
    (mono_state_auth (DfracOwn 1) s, mono_state_auth (DfracOwn 1) s) ~l~>
    (mono_state_auth (DfracOwn 1) s', mono_state_auth (DfracOwn 1) s').
  Proof.
    intros. apply auth_local_update.
    - apply mra_local_update_grow. done.
    - rewrite principal_included //.
    - done.
  Qed.
End sts.

#[global] Opaque mono_state_auth.
#[global] Opaque mono_state_lb.
