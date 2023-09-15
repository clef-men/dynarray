From ml Require Import
  prelude.
From ml.lang Require Import
  notations
  proofmode.
From ml.std Require Export
  base.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types l : loc.

  Definition record3_make : val :=
    λ: "v₀" "v₁" "v₂",
      let: "l" := AllocN #3 "v₀" in
      "l".(1) <- "v₁" ;;
      "l".(2) <- "v₂" ;;
      "l".

  Definition record3_model l dq v₀ v₁ v₂ : iProp Σ :=
    l.(0) ↦{dq} v₀ ∗
    l.(1) ↦{dq} v₁ ∗
    l.(2) ↦{dq} v₂.

  Lemma record3_model_eq l dq v₀ v₁ v₂ :
    record3_model l dq v₀ v₁ v₂ ⊣⊢
    l.(0) ↦{dq} v₀ ∗ l.(1) ↦{dq} v₁ ∗ l.(2) ↦{dq} v₂.
  Proof.
    done.
  Qed.
  Lemma record3_model_eq_1 l dq v₀ v₁ v₂ :
    record3_model l dq v₀ v₁ v₂ -∗
      l.(0) ↦{dq} v₀ ∗
      l.(1) ↦{dq} v₁ ∗
      l.(2) ↦{dq} v₂.
  Proof.
    done.
  Qed.
  Lemma record3_model_eq_2 l dq v₀ v₁ v₂ :
    l.(0) ↦{dq} v₀ -∗
    l.(1) ↦{dq} v₁ -∗
    l.(2) ↦{dq} v₂ -∗
    record3_model l dq v₀ v₁ v₂.
  Proof.
    rewrite /record3_model. auto with iFrame.
  Qed.

  #[global] Instance record3_model_timeless l dq v₀ v₁ v₂ :
    Timeless (record3_model l dq v₀ v₁ v₂).
  Proof.
    apply _.
  Qed.
  #[global] Instance record3_model_persistent l v₀ v₁ v₂ :
    Persistent (record3_model l DfracDiscarded v₀ v₁ v₂).
  Proof.
    apply _.
  Qed.

  #[global] Instance record3_model_fractional l v₀ v₁ v₂ :
    Fractional (λ q, record3_model l (DfracOwn q) v₀ v₁ v₂).
  Proof.
    apply _.
  Qed.
  #[global] Instance record3_model_as_fractional l q v₀ v₁ v₂ :
    AsFractional (record3_model l (DfracOwn q) v₀ v₁ v₂) (λ q, record3_model l (DfracOwn q) v₀ v₁ v₂) q.
  Proof.
    split; done || apply _.
  Qed.

  Lemma record3_model_valid l dq v₀ v₁ v₂ :
    record3_model l dq v₀ v₁ v₂ -∗
    ⌜✓ dq⌝.
  Proof.
    iIntros "(Hv₀ & Hv₁ & Hv₂)". iApply (mapsto_valid with "Hv₀").
  Qed.
  Lemma record3_model_combine l dq1 v₀1 v₁1 v₂1 dq2 v₀2 v₁2 v₂2 :
    record3_model l dq1 v₀1 v₁1 v₂1 -∗
    record3_model l dq2 v₀2 v₁2 v₂2 -∗
      record3_model l (dq1 ⋅ dq2) v₀1 v₁1 v₂1 ∗
      ⌜v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2⌝.
  Proof.
    iIntros "(Hv₀1 & Hv₁1 & Hv₂1) (Hv₀2 & Hv₁2 & Hv₂2)".
    iDestruct (mapsto_combine with "Hv₀1 Hv₀2") as "(Hv₀ & <-)".
    iDestruct (mapsto_combine with "Hv₁1 Hv₁2") as "(Hv₁ & <-)".
    iDestruct (mapsto_combine with "Hv₂1 Hv₂2") as "(Hv₂ & <-)".
    iSplit; last done. iFrame.
  Qed.
  Lemma record3_model_valid_2 l dq1 v₀1 v₁1 v₂1 dq2 v₀2 v₁2 v₂2 :
    record3_model l dq1 v₀1 v₁1 v₂1 -∗
    record3_model l dq2 v₀2 v₁2 v₂2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record3_model_combine with "Hl1 Hl2") as "(Hl & %)".
    iDestruct (record3_model_valid with "Hl") as %?.
    done.
  Qed.
  Lemma record3_model_agree l dq1 v₀1 v₁1 v₂1 dq2 v₀2 v₁2 v₂2 :
    record3_model l dq1 v₀1 v₁1 v₂1 -∗
    record3_model l dq2 v₀2 v₁2 v₂2 -∗
    ⌜v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record3_model_valid_2 with "Hl1 Hl2") as %?. naive_solver.
  Qed.
  Lemma record3_model_dfrac_ne l1 dq1 v₀1 v₁1 v₂1 l2 dq2 v₀2 v₁2 v₂2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    record3_model l1 dq1 v₀1 v₁1 v₂1 -∗
    record3_model l2 dq2 v₀2 v₁2 v₂2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "% Hl1 Hl2" (->).
    iDestruct (record3_model_valid_2 with "Hl1 Hl2") as %?. naive_solver.
  Qed.
  Lemma record3_model_ne l1 v₀1 v₁1 v₂1 l2 dq2 v₀2 v₁2 v₂2 :
    record3_model l1 (DfracOwn 1) v₀1 v₁1 v₂1 -∗
    record3_model l2 dq2 v₀2 v₁2 v₂2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iApply record3_model_dfrac_ne. intros []%exclusive_l. apply _.
  Qed.
  Lemma record3_model_exclusive l v₀1 v₁1 v₂1 v₀2 v₁2 v₂2 :
    record3_model l (DfracOwn 1) v₀1 v₁1 v₂1 -∗
    record3_model l (DfracOwn 1) v₀2 v₁2 v₂2 -∗
    False.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record3_model_ne with "Hl1 Hl2") as %?. naive_solver.
  Qed.
  Lemma record3_model_persist l dq v₀ v₁ v₂ :
    record3_model l dq v₀ v₁ v₂ ==∗
    record3_model l DfracDiscarded v₀ v₁ v₂.
  Proof.
    iIntros "(Hv₀ & Hv₁ & Hv₂)".
    iMod (mapsto_persist with "Hv₀") as "$".
    iMod (mapsto_persist with "Hv₁") as "$".
    iMod (mapsto_persist with "Hv₂") as "$".
    done.
  Qed.

  Lemma record3_dfrac_relax dq l v₀ v₁ v₂ :
    ✓ dq →
    record3_model l (DfracOwn 1) v₀ v₁ v₂ ==∗
    record3_model l dq v₀ v₁ v₂.
  Proof.
    iIntros "% (Hv₀ & Hv₁ & Hv₂)".
    iMod (mapsto_dfrac_relax with "Hv₀") as "Hv₀"; first done.
    iMod (mapsto_dfrac_relax with "Hv₁") as "Hv₁"; first done.
    iMod (mapsto_dfrac_relax with "Hv₂") as "Hv₂"; first done.
    iFrame. done.
  Qed.

  Lemma record3_make_spec v₀ v₁ v₂ :
    {{{ True }}}
      record3_make v₀ v₁ v₂
    {{{ l, RET #l; record3_model l (DfracOwn 1) v₀ v₁ v₂ ∗ meta_token l ⊤ }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_allocN with "[//]"); first done. iIntros "%l (Hl & Hmeta & _)". rewrite loc_add_0.
    wp_pures.
    iDestruct (array_cons with "Hl") as "(Hv₀ & Hl)".
    iEval (setoid_rewrite <- loc_add_0) in "Hv₀".
    iDestruct (array_cons with "Hl") as "(Hv₁ & Hl)".
    iDestruct (array_singleton with "Hl") as "Hv₂".
    rewrite loc_add_assoc Z.add_1_r -Z.two_succ.
    wp_store. wp_store.
    iApply "HΦ". iFrame. done.
  Qed.

  Lemma record3_get0_spec l dq v₀ v₁ v₂ :
    {{{ record3_model l dq v₀ v₁ v₂ }}}
      !#l.(0)
    {{{ RET v₀; record3_model l dq v₀ v₁ v₂ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂]").
  Qed.
  Lemma record3_get1_spec l dq v₀ v₁ v₂ :
    {{{ record3_model l dq v₀ v₁ v₂ }}}
      !#l.(1)
    {{{ RET v₁; record3_model l dq v₀ v₁ v₂ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂]").
  Qed.
  Lemma record3_get2_spec l dq v₀ v₁ v₂ :
    {{{ record3_model l dq v₀ v₁ v₂ }}}
      !#l.(2)
    {{{ RET v₂; record3_model l dq v₀ v₁ v₂ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂]").
  Qed.

  Lemma record3_set0_spec l v₀ v₁ v₂ v :
    {{{ record3_model l (DfracOwn 1) v₀ v₁ v₂ }}}
      #l.(0) <- v
    {{{ RET #(); record3_model l (DfracOwn 1) v v₁ v₂ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂]").
  Qed.
  Lemma record3_set1_spec l v₀ v₁ v₂ v :
    {{{ record3_model l (DfracOwn 1) v₀ v₁ v₂ }}}
      #l.(1) <- v
    {{{ RET #(); record3_model l (DfracOwn 1) v₀ v v₂ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂]").
  Qed.
  Lemma record3_set2_spec l v₀ v₁ v₂ v :
    {{{ record3_model l (DfracOwn 1) v₀ v₁ v₂ }}}
      #l.(2) <- v
    {{{ RET #(); record3_model l (DfracOwn 1) v₀ v₁ v }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂]").
  Qed.
End heapGS.

#[global] Opaque record3_make.

#[global] Opaque record3_model.
