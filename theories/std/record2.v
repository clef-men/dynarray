From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  notations
  proofmode.
From heap_lang.std Require Export
  base.

Section heap_GS.
  Context `{heap_GS : !heapGS Σ}.

  Implicit Types l : loc.

  Definition record2_make : val :=
    λ: "v₀" "v₁",
      let: "l" := AllocN #2 "v₀" in
      "l".[1] <- "v₁" ;;
      "l".

  Definition record2_model l dq v₀ v₁ : iProp Σ :=
    l.[0] ↦{dq} v₀ ∗
    l.[1] ↦{dq} v₁.

  Lemma record2_model_eq l dq v₀ v₁ :
    record2_model l dq v₀ v₁ ⊣⊢
    l.[0] ↦{dq} v₀ ∗ l.[1] ↦{dq} v₁.
  Proof.
    iSmash.
  Qed.
  Lemma record2_model_eq_1 l dq v₀ v₁ :
    record2_model l dq v₀ v₁ ⊢
      l.[0] ↦{dq} v₀ ∗
      l.[1] ↦{dq} v₁.
  Proof.
    iSmash.
  Qed.
  Lemma record2_model_eq_2 l dq v₀ v₁ :
    l.[0] ↦{dq} v₀ -∗
    l.[1] ↦{dq} v₁ -∗
    record2_model l dq v₀ v₁.
  Proof.
    iSmash.
  Qed.

  #[global] Instance record2_model_timeless l dq v₀ v₁ :
    Timeless (record2_model l dq v₀ v₁).
  Proof.
    apply _.
  Qed.
  #[global] Instance record2_model_persistent l v₀ v₁ :
    Persistent (record2_model l DfracDiscarded v₀ v₁).
  Proof.
    apply _.
  Qed.

  #[global] Instance record2_model_fractional l v₀ v₁ :
    Fractional (λ q, record2_model l (DfracOwn q) v₀ v₁).
  Proof.
    apply _.
  Qed.
  #[global] Instance record2_model_as_fractional l q v₀ v₁ :
    AsFractional (record2_model l (DfracOwn q) v₀ v₁) (λ q, record2_model l (DfracOwn q) v₀ v₁) q.
  Proof.
    split; done || apply _.
  Qed.

  Lemma record2_model_valid l dq v₀ v₁ :
    record2_model l dq v₀ v₁ ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "(Hv₀ & Hv₁)". iApply (mapsto_valid with "Hv₀").
  Qed.
  Lemma record2_model_combine l dq1 v₀1 v₁1 dq2 v₀2 v₁2 :
    record2_model l dq1 v₀1 v₁1 -∗
    record2_model l dq2 v₀2 v₁2 -∗
      record2_model l (dq1 ⋅ dq2) v₀1 v₁1 ∗
      ⌜v₀1 = v₀2 ∧ v₁1 = v₁2⌝.
  Proof.
    iIntros "(Hv₀1 & Hv₁1) (Hv₀2 & Hv₁2)".
    iDestruct (mapsto_combine with "Hv₀1 Hv₀2") as "(Hv₀ & <-)".
    iDestruct (mapsto_combine with "Hv₁1 Hv₁2") as "(Hv₁ & <-)".
    iSmash.
  Qed.
  Lemma record2_model_valid_2 l dq1 v₀1 v₁1 dq2 v₀2 v₁2 :
    record2_model l dq1 v₀1 v₁1 -∗
    record2_model l dq2 v₀2 v₁2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ v₀1 = v₀2 ∧ v₁1 = v₁2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record2_model_combine with "Hl1 Hl2") as "(Hl & %)".
    iDestruct (record2_model_valid with "Hl") as %?.
    iSmash+.
  Qed.
  Lemma record2_model_agree l dq1 v₀1 v₁1 dq2 v₀2 v₁2 :
    record2_model l dq1 v₀1 v₁1 -∗
    record2_model l dq2 v₀2 v₁2 -∗
    ⌜v₀1 = v₀2 ∧ v₁1 = v₁2⌝.
  Proof.
    iSmash.
  Qed.
  Lemma record2_model_dfrac_ne l1 dq1 v₀1 v₁1 l2 dq2 v₀2 v₁2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    record2_model l1 dq1 v₀1 v₁1 -∗
    record2_model l2 dq2 v₀2 v₁2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "% Hl1 Hl2" (->).
    iDestruct (record2_model_valid_2 with "Hl1 Hl2") as %?.
    naive_solver.
  Qed.
  Lemma record2_model_ne l1 v₀1 v₁1 l2 dq2 v₀2 v₁2 :
    record2_model l1 (DfracOwn 1) v₀1 v₁1 -∗
    record2_model l2 dq2 v₀2 v₁2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iSmash.
  Qed.
  Lemma record2_model_exclusive l v₀1 v₁1 v₀2 v₁2 :
    record2_model l (DfracOwn 1) v₀1 v₁1 -∗
    record2_model l (DfracOwn 1) v₀2 v₁2 -∗
    False.
  Proof.
    iSmash.
  Qed.
  Lemma record2_model_persist l dq v₀ v₁ :
    record2_model l dq v₀ v₁ ⊢ |==>
    record2_model l DfracDiscarded v₀ v₁.
  Proof.
    iSmash.
  Qed.

  Lemma record2_dfrac_relax dq l v₀ v₁ :
    ✓ dq →
    record2_model l (DfracOwn 1) v₀ v₁ ⊢ |==>
    record2_model l dq v₀ v₁.
  Proof.
    iIntros "% (Hv₀ & Hv₁)".
    iMod (mapsto_dfrac_relax with "Hv₀") as "Hv₀"; first done.
    iMod (mapsto_dfrac_relax with "Hv₁") as "Hv₁"; first done.
    iSmash.
  Qed.

  Lemma record2_make_spec v₀ v₁ :
    {{{ True }}}
      record2_make v₀ v₁
    {{{ l,
      RET #l;
      record2_model l (DfracOwn 1) v₀ v₁ ∗
      meta_token l ⊤
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_allocN with "[//]"); first done. iIntros "%l (Hl & Hmeta & _)". rewrite Loc.add_0.
    wp_pures.
    iDestruct (array_cons with "Hl") as "(Hv₀ & Hl)".
    iEval (setoid_rewrite <- Loc.add_0) in "Hv₀".
    iSmash.
  Qed.

  Lemma record2_get0_spec l dq v₀ v₁ :
    {{{
      record2_model l dq v₀ v₁
    }}}
      !#l.[0]
    {{{
      RET v₀;
      record2_model l dq v₀ v₁
    }}}.
  Proof.
    iSmash.
  Qed.
  Lemma record2_get1_spec l dq v₀ v₁ :
    {{{
      record2_model l dq v₀ v₁
    }}}
      !#l.[1]
    {{{
      RET v₁;
      record2_model l dq v₀ v₁
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma record2_set0_spec l v₀ v₁ v :
    {{{
      record2_model l (DfracOwn 1) v₀ v₁
    }}}
      #l.[0] <- v
    {{{
      RET #();
      record2_model l (DfracOwn 1) v v₁
    }}}.
  Proof.
    iSmash.
  Qed.
  Lemma record2_set1_spec l v₀ v₁ v :
    {{{
      record2_model l (DfracOwn 1) v₀ v₁
    }}}
      #l.[1] <- v
    {{{
      RET #();
      record2_model l (DfracOwn 1) v₀ v
    }}}.
  Proof.
    iSmash.
  Qed.
End heap_GS.

#[global] Opaque record2_make.

#[global] Opaque record2_model.
