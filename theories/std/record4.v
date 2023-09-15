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

  Definition record4_make : val :=
    λ: "v₀" "v₁" "v₂" "v₃",
      let: "l" := AllocN #4 "v₀" in
      "l".(1) <- "v₁" ;;
      "l".(2) <- "v₂" ;;
      "l".(3) <- "v₃" ;;
      "l".

  Definition record4_model l dq v₀ v₁ v₂ v₃ : iProp Σ :=
    l.(0) ↦{dq} v₀ ∗
    l.(1) ↦{dq} v₁ ∗
    l.(2) ↦{dq} v₂ ∗
    l.(3) ↦{dq} v₃.

  Lemma record4_model_eq l dq v₀ v₁ v₂ v₃ :
    record4_model l dq v₀ v₁ v₂ v₃ ⊣⊢
    l.(0) ↦{dq} v₀ ∗ l.(1) ↦{dq} v₁ ∗ l.(2) ↦{dq} v₂ ∗ l.(3) ↦{dq} v₃.
  Proof.
    done.
  Qed.
  Lemma record4_model_eq_1 l dq v₀ v₁ v₂ v₃ :
    record4_model l dq v₀ v₁ v₂ v₃ -∗
      l.(0) ↦{dq} v₀ ∗
      l.(1) ↦{dq} v₁ ∗
      l.(2) ↦{dq} v₂ ∗
      l.(3) ↦{dq} v₃.
  Proof.
    done.
  Qed.
  Lemma record4_model_eq_2 l dq v₀ v₁ v₂ v₃ :
    l.(0) ↦{dq} v₀ -∗
    l.(1) ↦{dq} v₁ -∗
    l.(2) ↦{dq} v₂ -∗
    l.(3) ↦{dq} v₃ -∗
    record4_model l dq v₀ v₁ v₂ v₃.
  Proof.
   rewrite /record4_model. auto with iFrame.
  Qed.

  #[global] Instance record4_model_timeless l dq v₀ v₁ v₂ v₃ :
    Timeless (record4_model l dq v₀ v₁ v₂ v₃).
  Proof.
    apply _.
  Qed.
  #[global] Instance record4_model_persistent l v₀ v₁ v₂ v₃ :
    Persistent (record4_model l DfracDiscarded v₀ v₁ v₂ v₃).
  Proof.
    apply _.
  Qed.

  #[global] Instance record4_model_fractional l v₀ v₁ v₂ v₃ :
    Fractional (λ q, record4_model l (DfracOwn q) v₀ v₁ v₂ v₃).
  Proof.
    apply _.
  Qed.
  #[global] Instance record4_model_as_fractional l q v₀ v₁ v₂ v₃ :
    AsFractional (record4_model l (DfracOwn q) v₀ v₁ v₂ v₃) (λ q, record4_model l (DfracOwn q) v₀ v₁ v₂ v₃) q.
  Proof.
    split; done || apply _.
  Qed.

  Lemma record4_model_valid l dq v₀ v₁ v₂ v₃ :
    record4_model l dq v₀ v₁ v₂ v₃ -∗
    ⌜✓ dq⌝.
  Proof.
    iIntros "(Hv₀ & Hv₁ & Hv₂ & Hv₃)". iApply (mapsto_valid with "Hv₀").
  Qed.
  Lemma record4_model_combine l dq1 v₀1 v₁1 v₂1 v₃1 dq2 v₀2 v₁2 v₂2 v₃2 :
    record4_model l dq1 v₀1 v₁1 v₂1 v₃1 -∗
    record4_model l dq2 v₀2 v₁2 v₂2 v₃2 -∗
      record4_model l (dq1 ⋅ dq2) v₀1 v₁1 v₂1 v₃1 ∗
      ⌜v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2 ∧ v₃1 = v₃2⌝.
  Proof.
    iIntros "(Hv₀1 & Hv₁1 & Hv₂1 & Hv₃1) (Hv₀2 & Hv₁2 & Hv₂2 & Hv₃2)".
    iDestruct (mapsto_combine with "Hv₀1 Hv₀2") as "(Hv₀ & <-)".
    iDestruct (mapsto_combine with "Hv₁1 Hv₁2") as "(Hv₁ & <-)".
    iDestruct (mapsto_combine with "Hv₂1 Hv₂2") as "(Hv₂ & <-)".
    iDestruct (mapsto_combine with "Hv₃1 Hv₃2") as "(Hv₃ & <-)".
    iSplit; last done. iFrame.
  Qed.
  Lemma record4_model_valid_2 l dq1 v₀1 v₁1 v₂1 v₃1 dq2 v₀2 v₁2 v₂2 v₃2 :
    record4_model l dq1 v₀1 v₁1 v₂1 v₃1 -∗
    record4_model l dq2 v₀2 v₁2 v₂2 v₃2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2 ∧ v₃1 = v₃2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record4_model_combine with "Hl1 Hl2") as "(Hl & %)".
    iDestruct (record4_model_valid with "Hl") as %?.
    done.
  Qed.
  Lemma record4_model_agree l dq1 v₀1 v₁1 v₂1 v₃1 dq2 v₀2 v₁2 v₂2 v₃2 :
    record4_model l dq1 v₀1 v₁1 v₂1 v₃1 -∗
    record4_model l dq2 v₀2 v₁2 v₂2 v₃2 -∗
    ⌜v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2 ∧ v₃1 = v₃2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record4_model_valid_2 with "Hl1 Hl2") as %?. naive_solver.
  Qed.
  Lemma record4_model_dfrac_ne l1 dq1 v₀1 v₁1 v₂1 v₃1 l2 dq2 v₀2 v₁2 v₂2 v₃2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    record4_model l1 dq1 v₀1 v₁1 v₂1 v₃1 -∗
    record4_model l2 dq2 v₀2 v₁2 v₂2 v₃2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "% Hl1 Hl2" (->).
    iDestruct (record4_model_valid_2 with "Hl1 Hl2") as %?. naive_solver.
  Qed.
  Lemma record4_model_ne l1 v₀1 v₁1 v₂1 v₃1 l2 dq2 v₀2 v₁2 v₂2 v₃2 :
    record4_model l1 (DfracOwn 1) v₀1 v₁1 v₂1 v₃1 -∗
    record4_model l2 dq2 v₀2 v₁2 v₂2 v₃2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iApply record4_model_dfrac_ne. intros []%exclusive_l. apply _.
  Qed.
  Lemma record4_model_exclusive l v₀1 v₁1 v₂1 v₃1 v₀2 v₁2 v₂2 v₃2 :
    record4_model l (DfracOwn 1) v₀1 v₁1 v₂1 v₃1 -∗
    record4_model l (DfracOwn 1) v₀2 v₁2 v₂2 v₃2 -∗
    False.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record4_model_ne with "Hl1 Hl2") as %?. naive_solver.
  Qed.
  Lemma record4_model_persist l dq v₀ v₁ v₂ v₃ :
    record4_model l dq v₀ v₁ v₂ v₃ ==∗
    record4_model l DfracDiscarded v₀ v₁ v₂ v₃.
  Proof.
    iIntros "(Hv₀ & Hv₁ & Hv₂ & Hv₃)".
    iMod (mapsto_persist with "Hv₀") as "$".
    iMod (mapsto_persist with "Hv₁") as "$".
    iMod (mapsto_persist with "Hv₂") as "$".
    iMod (mapsto_persist with "Hv₃") as "$".
    done.
  Qed.

  Lemma record4_dfrac_relax dq l v₀ v₁ v₂ v₃ :
    ✓ dq →
    record4_model l (DfracOwn 1) v₀ v₁ v₂ v₃ ==∗
    record4_model l dq v₀ v₁ v₂ v₃.
  Proof.
    iIntros "% (Hv₀ & Hv₁ & Hv₂ & Hv₃)".
    iMod (mapsto_dfrac_relax with "Hv₀") as "Hv₀"; first done.
    iMod (mapsto_dfrac_relax with "Hv₁") as "Hv₁"; first done.
    iMod (mapsto_dfrac_relax with "Hv₂") as "Hv₂"; first done.
    iMod (mapsto_dfrac_relax with "Hv₃") as "Hv₃"; first done.
    iFrame. done.
  Qed.

  Lemma record4_make_spec v₀ v₁ v₂ v₃ :
    {{{ True }}}
      record4_make v₀ v₁ v₂ v₃
    {{{ l, RET #l; record4_model l (DfracOwn 1) v₀ v₁ v₂ v₃ ∗ meta_token l ⊤ }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_allocN with "[//]"); first done. iIntros "%l (Hl & Hmeta & _)". rewrite loc_add_0.
    wp_pures.
    iDestruct (array_cons with "Hl") as "(Hv₀ & Hl)".
    iEval (setoid_rewrite <- loc_add_0) in "Hv₀".
    iDestruct (array_cons with "Hl") as "(Hv₁ & Hl)".
    iDestruct (array_cons with "Hl") as "(Hv₂ & Hl)".
    rewrite loc_add_assoc Z.add_1_r -Z.two_succ.
    iDestruct (array_singleton with "Hl") as "Hv₃".
    rewrite loc_add_assoc Z.add_1_r. assert (Z.succ 2 = 3)%Z as -> by lia.
    wp_store. wp_store. wp_store.
    iApply "HΦ". iFrame. done.
  Qed.

  Lemma record4_get0_spec l dq v₀ v₁ v₂ v₃ :
    {{{ record4_model l dq v₀ v₁ v₂ v₃ }}}
      !#l.(0)
    {{{ RET v₀; record4_model l dq v₀ v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
  Lemma record4_get1_spec l dq v₀ v₁ v₂ v₃ :
    {{{ record4_model l dq v₀ v₁ v₂ v₃ }}}
      !#l.(1)
    {{{ RET v₁; record4_model l dq v₀ v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
  Lemma record4_get2_spec l dq v₀ v₁ v₂ v₃ :
    {{{ record4_model l dq v₀ v₁ v₂ v₃ }}}
      !#l.(2)
    {{{ RET v₂; record4_model l dq v₀ v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
  Lemma record4_get3_spec l dq v₀ v₁ v₂ v₃ :
    {{{ record4_model l dq v₀ v₁ v₂ v₃ }}}
      !#l.(3)
    {{{ RET v₃; record4_model l dq v₀ v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.

  Lemma record4_set0_spec l v₀ v₁ v₂ v₃ v :
    {{{ record4_model l (DfracOwn 1) v₀ v₁ v₂ v₃ }}}
      #l.(0) <- v
    {{{ RET #(); record4_model l (DfracOwn 1) v v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
  Lemma record4_set1_spec l v₀ v₁ v₂ v₃ v :
    {{{ record4_model l (DfracOwn 1) v₀ v₁ v₂ v₃ }}}
      #l.(1) <- v
    {{{ RET #(); record4_model l (DfracOwn 1) v₀ v v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
  Lemma record4_set2_spec l v₀ v₁ v₂ v₃ v :
    {{{ record4_model l (DfracOwn 1) v₀ v₁ v₂ v₃ }}}
      #l.(2) <- v
    {{{ RET #(); record4_model l (DfracOwn 1) v₀ v₁ v v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
End heapGS.

#[global] Opaque record4_make.

#[global] Opaque record4_model.
