From ml Require Import
  prelude.
From ml.bi Require Import
  big_op.
From ml.language Require Import
  notations
  proofmode.
From ml.std Require Export
  base.

Section heapGS.
  Context `{!heapGS Σ}.

  Implicit Types i : nat.
  Implicit Types l : loc.
  Implicit Types v t fn acc : val.
  Implicit Types vs : list val.

  Definition chunk_make : val :=
    λ: "sz" "v",
      if: #0 < "sz" then (
        AllocN "sz" "v"
      ) else (
        #(inhabitant : loc)
      ).

  #[local] Definition chunk_init_aux : val :=
    rec: "chunk_init_aux" "t" "sz" "fn" "i" :=
      if: "i" = "sz" then (
        #()
      ) else (
        "t" +ₗ "i" <- "fn" "i" ;;
        "chunk_init_aux" "t" "sz" "fn" ("i" + #1)
      ).
  Definition chunk_init : val :=
    λ: "sz" "fn",
      let: "t" := chunk_make "sz" #() in
      chunk_init_aux "t" "sz" "fn" #0 ;;
      "t".

  #[local] Definition chunk_foldli_aux : val :=
    rec: "chunk_foldli_aux" "t" "sz" "acc" "fn" "i" :=
      if: "i" = "sz" then (
        "acc"
      ) else (
        "chunk_foldli_aux" "t" "sz" ("fn" "acc" "i" !("t" +ₗ "i")) "fn" ("i" + #1)
      ).
  Definition chunk_foldli : val :=
    λ: "t" "sz" "acc" "fn",
      chunk_foldli_aux "t" "sz" "acc" "fn" #0.
  Definition chunk_foldl : val :=
    λ: "t" "sz" "acc" "fn",
      chunk_foldli "t" "sz" "acc" (λ: "acc" <> "v", "fn" "acc" "v").

  #[local] Definition chunk_foldri_aux : val :=
    rec: "chunk_foldri_aux" "t" "fn" "acc" "i" :=
      if: "i" = #0 then (
        "acc"
      ) else (
        let: "i" := "i" - #1 in
        "chunk_foldri_aux" "t" "fn" ("fn" "i" !("t" +ₗ "i") "acc") "i"
      ).
  Definition chunk_foldri : val :=
    λ: "t" "sz" "fn" "acc",
      chunk_foldri_aux "t" "fn" "acc" "sz".
  Definition chunk_foldr : val :=
    λ: "t" "sz" "fn" "acc",
      chunk_foldri "t" "sz" (λ: <> "v" "acc", "fn" "v" "acc") "acc".

  Definition chunk_iteri : val :=
    λ: "t" "sz" "fn",
      chunk_foldli "t" "sz" #() (λ: <> "i" "v", "fn" "i" "v" ;; #()).
  Definition chunk_iter : val :=
    λ: "t" "sz" "fn",
      chunk_iteri "t" "sz" (λ: <> "v", "fn" "v").

  Definition chunk_mapi : val :=
    λ: "t" "sz" "fn",
      chunk_init "sz" (λ: "i", "fn" "i" !("t" +ₗ "i")).
  Definition chunk_map : val :=
    λ: "t" "sz" "fn",
      chunk_mapi "t" "sz" (λ: <> "v", "fn" "v").

  Definition chunk_copy : val :=
    λ: "t" "sz" "t'",
      chunk_iteri "t" "sz" (λ: "i" "v", "t'" +ₗ "i" <- "v").

  Definition chunk_grow : val :=
    λ: "t" "sz" "sz'" "v",
      let: "t'" := chunk_make "sz'" "v" in
      chunk_copy "t" "sz" "t'" ;;
      "t'".
  Definition chunk_shrink : val :=
    λ: "t" "sz" "sz'",
      let: "t'" := chunk_make "sz'" #() in
      chunk_copy "t" "sz'" "t'" ;;
      "t'".

  Definition chunk_clone : val :=
    λ: "t" "sz",
      chunk_shrink "t" "sz" "sz".

  Section chunk_model.
    Definition chunk_model l dq vs : iProp Σ :=
      [∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v.

    #[global] Instance chunk_model_timeless l dq vs :
      Timeless (chunk_model l dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk_model_persistent l vs :
      Persistent (chunk_model l DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_model_fractional l vs :
      Fractional (λ q, chunk_model l (DfracOwn q) vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk_model_as_fractional l q vs :
      AsFractional (chunk_model l (DfracOwn q) vs) (λ q, chunk_model l (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk_model_nil l dq :
      ⊢ chunk_model l dq [].
    Proof.
      rewrite /chunk_model //.
    Qed.

    Lemma chunk_model_singleton l dq v :
      l ↦{dq} v ⊣⊢
      chunk_model l dq [v].
    Proof.
      setoid_rewrite big_sepL_singleton. rewrite Loc.add_0 //.
    Qed.
    Lemma chunk_model_singleton_1 l dq v :
      l ↦{dq} v ⊢
      chunk_model l dq [v].
    Proof.
      rewrite chunk_model_singleton //.
    Qed.
    Lemma chunk_model_singleton_2 l dq v :
      chunk_model l dq [v] ⊢
      l ↦{dq} v.
    Proof.
      rewrite chunk_model_singleton //.
    Qed.

    Lemma chunk_model_cons l dq v vs :
      l ↦{dq} v ∗ chunk_model (l +ₗ 1) dq vs ⊣⊢
      chunk_model l dq (v :: vs).
    Proof.
      setoid_rewrite big_sepL_cons.
      setoid_rewrite Nat2Z.inj_succ.
      setoid_rewrite <- Z.add_1_l.
      setoid_rewrite <- Loc.add_assoc.
      rewrite Loc.add_0 //.
    Qed.
    Lemma chunk_model_cons_1 l dq v vs :
      l ↦{dq} v -∗
      chunk_model (l +ₗ 1) dq vs -∗
      chunk_model l dq (v :: vs).
    Proof.
      rewrite -chunk_model_cons. iSmash.
    Qed.
    Lemma chunk_model_cons_2 l dq v vs :
      chunk_model l dq (v :: vs) ⊢
        l ↦{dq} v ∗
        chunk_model (l +ₗ 1) dq vs.
    Proof.
      rewrite chunk_model_cons //.
    Qed.
    #[global] Instance chunk_model_cons_frame l dq v vs R Q :
      Frame false R (l ↦{dq} v ∗ chunk_model (l +ₗ 1) dq vs) Q →
      Frame false R (chunk_model l dq (v :: vs)) Q
      | 2.
    Proof.
      rewrite /Frame chunk_model_cons //.
    Qed.

    Lemma chunk_model_app l dq vs1 vs2 :
      chunk_model l dq vs1 ∗ chunk_model (l +ₗ length vs1) dq vs2 ⊣⊢
      chunk_model l dq (vs1 ++ vs2).
    Proof.
      setoid_rewrite big_sepL_app.
      setoid_rewrite Nat2Z.inj_add.
      setoid_rewrite <- Loc.add_assoc. done.
    Qed.
    Lemma chunk_model_app_1 l dq vs1 vs2 sz :
      sz = length vs1 →
      chunk_model l dq vs1 -∗
      chunk_model (l +ₗ sz) dq vs2 -∗
      chunk_model l dq (vs1 ++ vs2).
    Proof.
      intros ->. rewrite -chunk_model_app. iSmash.
    Qed.
    Lemma chunk_model_app_2 l dq vs vs1 vs2 :
      vs = vs1 ++ vs2 →
      chunk_model l dq vs ⊢
        chunk_model l dq vs1 ∗
        chunk_model (l +ₗ length vs1) dq vs2.
    Proof.
      intros ->. rewrite chunk_model_app //.
    Qed.

    Lemma chunk_model_update {l dq vs} i v :
      vs !! i = Some v →
      chunk_model l dq vs ⊢
        (l +ₗ i) ↦{dq} v ∗
        (∀ w, (l +ₗ i) ↦{dq} w -∗ chunk_model l dq (<[i := w]> vs)).
    Proof.
      intros. iApply big_sepL_insert_acc. done.
    Qed.
    Lemma chunk_model_lookup_acc {l dq vs} i v :
      vs !! i = Some v →
      chunk_model l dq vs ⊢
        (l +ₗ i) ↦{dq} v ∗
        ((l +ₗ i) ↦{dq} v -∗ chunk_model l dq vs).
    Proof.
      intros. iApply big_sepL_lookup_acc. done.
    Qed.
    Lemma chunk_model_lookup {l dq vs} i v :
      vs !! i = Some v →
      chunk_model l dq vs ⊢
      (l +ₗ i) ↦{dq} v.
    Proof.
      intros. iApply big_sepL_lookup. done.
    Qed.

    Lemma chunk_model_valid l dq vs :
      0 < length vs →
      chunk_model l dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% Hmodel".
      iDestruct (chunk_model_update 0 with "Hmodel") as "(H↦ & _)".
      { destruct (nth_lookup_or_length vs 0 inhabitant); [done | lia]. }
      iApply (mapsto_valid with "H↦").
    Qed.
    Lemma chunk_model_combine l dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_model l dq1 vs1 -∗
      chunk_model l dq2 vs2 -∗
        chunk_model l (dq1 ⋅ dq2) vs1 ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iInduction vs1 as [| v1 vs1] "IH" forall (l vs2); iIntros "% Hmodel1 Hmodel2".
      - rewrite (nil_length_inv vs2); last done. naive_solver.
      - destruct vs2 as [| v2 vs2]; first iSmash.
        iDestruct (chunk_model_cons_2 with "Hmodel1") as "(H↦1 & Hmodel1)".
        iDestruct (chunk_model_cons_2 with "Hmodel2") as "(H↦2 & Hmodel2)".
        iDestruct (mapsto_combine with "H↦1 H↦2") as "(H↦ & ->)".
        iDestruct ("IH" with "[] Hmodel1 Hmodel2") as "(Hmodel & ->)"; first iSmash. iSplit; last iSmash.
        iApply (chunk_model_cons_1 with "H↦ Hmodel").
    Qed.
    Lemma chunk_model_valid_2 l dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_model l dq1 vs1 -∗
      chunk_model l dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & ->)"; first done.
      iDestruct (chunk_model_valid with "Hmodel") as %?; first done.
      iSmash.
    Qed.
    Lemma chunk_model_agree l dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_model l dq1 vs1 -∗
      chunk_model l dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(_ & ->)"; first done.
      iSmash.
    Qed.
    Lemma chunk_model_dfrac_ne l1 dq1 vs1 l2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk_model l1 dq1 vs1 -∗
      chunk_model l2 dq2 vs2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      iIntros "% % % Hmodel1 Hmodel2" (->).
      iDestruct (chunk_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma chunk_model_ne l1 vs1 l2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_model l1 (DfracOwn 1) vs1 -∗
      chunk_model l2 dq2 vs2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      intros. iApply chunk_model_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk_model_exclusive l vs1 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_model l (DfracOwn 1) vs1 -∗
      chunk_model l (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (chunk_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma chunk_model_persist l dq vs :
      chunk_model l dq vs ⊢ |==>
      chunk_model l DfracDiscarded vs.
    Proof.
      iIntros "Hmodel".
      iApply big_sepL_bupd. iApply (big_sepL_impl with "Hmodel"). iIntros "!> %i %v %".
      iSmash.
    Qed.
  End chunk_model.

  Section chunk_span.
    Definition chunk_span l dq sz : iProp Σ :=
      ∃ vs,
      ⌜length vs = sz⌝ ∗
      chunk_model l dq vs.

    #[global] Instance chunk_span_timeless l dq sz :
      Timeless (chunk_span l dq sz).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk_span_persistent l sz :
      Persistent (chunk_span l DfracDiscarded sz).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_span_fractional l sz :
      Fractional (λ q, chunk_span l (DfracOwn q) sz).
    Proof.
      intros q1 q2. rewrite /chunk_span. setoid_rewrite chunk_model_fractional. iSplit; first iSmash.
      iIntros "((%vs & % & Hmodel1) & (%_vs & % & Hmodel2))".
      iDestruct (chunk_model_agree with "Hmodel1 Hmodel2") as %<-; first naive_solver.
      iSmash.
    Qed.
    #[global] Instance chunk_span_as_fractional l q sz :
      AsFractional (chunk_span l (DfracOwn q) sz) (λ q, chunk_span l (DfracOwn q) sz) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk_span_singleton l dq :
      (∃ v, l ↦{dq} v) ⊣⊢
      chunk_span l dq 1.
    Proof.
      setoid_rewrite chunk_model_singleton. iSplit.
      - iIntros "(%v & Hmodel)".
        iExists [v]. iSmash.
      - iIntros "(%vs & % & Hmodel)".
        destruct vs as [| v vs]; first iSmash. destruct vs; iSmash.
    Qed.
    Lemma chunk_span_singleton_1 l dq v :
      l ↦{dq} v ⊢
      chunk_span l dq 1.
    Proof.
      rewrite -chunk_span_singleton. iSmash.
    Qed.
    Lemma chunk_span_singleton_2 l dq :
      chunk_span l dq 1 ⊢
      ∃ v, l ↦{dq} v.
    Proof.
      rewrite chunk_span_singleton. iSmash.
    Qed.

    Lemma chunk_span_cons l dq sz :
      (∃ v, l ↦{dq} v ∗ chunk_span (l +ₗ 1) dq sz) ⊣⊢
      chunk_span l dq (S sz).
    Proof.
      iSplit.
      - iIntros "(%v & H↦ & (%vs & % & Hmodel))".
        iExists (v :: vs). iSplit; first iSmash.
        iApply (chunk_model_cons_1 with "H↦ Hmodel").
      - iIntros "(%vs & % & Hmodel)".
        destruct vs as [| v vs]; first iSmash.
        iDestruct (chunk_model_cons_2 with "Hmodel") as "(H↦ & Hmodel)".
        iExists v. iFrame. iExists vs. auto.
    Qed.
    Lemma chunk_span_cons_1 l dq v sz :
      l ↦{dq} v -∗
      chunk_span (l +ₗ 1) dq sz -∗
      chunk_span l dq (S sz).
    Proof.
      rewrite -chunk_span_cons. iSmash.
    Qed.
    Lemma chunk_span_cons_2 l dq sz :
      chunk_span l dq (S sz) ⊢
        ∃ v,
        l ↦{dq} v ∗
        chunk_span (l +ₗ 1) dq sz.
    Proof.
      rewrite chunk_span_cons //.
    Qed.
    #[global] Instance chunk_span_cons_frame l dq v sz R Q :
      Frame false R (l ↦{dq} v ∗ chunk_span (l +ₗ 1) dq sz) Q →
      Frame false R (chunk_span l dq (S sz)) Q
      | 2.
    Proof.
      rewrite /Frame. setoid_rewrite <- chunk_span_cons. intros H.
      iPoseProof H as "H". iSmash.
    Qed.

    Lemma chunk_span_app l dq sz1 sz2 :
      chunk_span l dq sz1 ∗ chunk_span (l +ₗ sz1) dq sz2 ⊣⊢
      chunk_span l dq (sz1 + sz2).
    Proof.
      iSplit.
      - iIntros "((%vs1 & % & Hmodel1) & (%vs2 & % & Hmodel2))".
        iExists (vs1 ++ vs2). iSplit; first (rewrite app_length; naive_solver).
        iApply (chunk_model_app_1 with "Hmodel1 Hmodel2"); first done.
      - iIntros "(%vs & % & Hmodel)".
        iDestruct (chunk_model_app_2 _ _ _ (take sz1 vs) (drop sz1 vs) with "Hmodel") as "(Hmodel1 & Hmodel2)"; first rewrite take_drop //.
        iSplitL "Hmodel1".
        + iExists (take sz1 vs). iFrame. rewrite take_length_le //. lia.
        + iExists (drop sz1 vs). rewrite take_length_le; last lia. iFrame.
          rewrite drop_length. iSmash.
    Qed.
    Lemma chunk_span_app_1 l dq sz1 sz2 :
      chunk_span l dq sz1 -∗
      chunk_span (l +ₗ sz1) dq sz2 -∗
      chunk_span l dq (sz1 + sz2).
    Proof.
      rewrite -chunk_span_app. iSmash.
    Qed.
    Lemma chunk_span_app_2 l dq sz sz1 sz2 :
      sz = sz1 + sz2 →
      chunk_span l dq sz ⊢
        chunk_span l dq sz1 ∗
        chunk_span (l +ₗ sz1) dq sz2.
    Proof.
      intros ->. rewrite chunk_span_app //.
    Qed.

    Lemma chunk_span_update {l dq sz} i :
      i < sz →
      chunk_span l dq sz ⊢
        ∃ v,
        (l +ₗ i) ↦{dq} v ∗
        (∀ w, (l +ₗ i) ↦{dq} w -∗ chunk_span l dq sz).
    Proof.
      iIntros "% (%vs & % & Hmodel)".
      iDestruct (chunk_model_update i with "Hmodel") as "(H↦ & Hmodel)".
      { rewrite list_lookup_lookup_total_lt; naive_solver. }
      iExists (vs !!! i). iFrame. iIntros "%v H↦".
      iExists (<[i := v]> vs). iSplit; first rewrite insert_length //.
      iSmash.
    Qed.
    Lemma chunk_span_lookup_acc {l dq sz} i :
      i < sz →
      chunk_span l dq sz ⊢
        ∃ v,
        (l +ₗ i) ↦{dq} v ∗
        ((l +ₗ i) ↦{dq} v -∗ chunk_span l dq sz).
    Proof.
      iIntros "% Hspan".
      iDestruct (chunk_span_update with "Hspan") as "(%v & H↦ & Hspan)"; first done.
      auto with iFrame.
    Qed.
    Lemma chunk_span_lookup {l dq sz} i :
      i < sz →
      chunk_span l dq sz ⊢
        ∃ v,
        (l +ₗ i) ↦{dq} v.
    Proof.
      iIntros "% Hspan".
      iDestruct (chunk_span_lookup_acc with "Hspan") as "(%v & H↦ & _)"; first done.
      iSmash.
    Qed.

    Lemma chunk_span_valid l dq sz :
      0 < sz →
      chunk_span l dq sz ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%vs & % & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first naive_solver.
    Qed.
    Lemma chunk_span_combine l dq1 sz1 dq2 sz2 :
      sz1 = sz2 →
      chunk_span l dq1 sz1 -∗
      chunk_span l dq2 sz2 -∗
        chunk_span l (dq1 ⋅ dq2) sz1.
    Proof.
      iIntros (<-) "(%vs1 & % & Hmodel1) (%vs2 & % & Hmodel2)".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & <-)"; first naive_solver.
      iSmash.
    Qed.
    Lemma chunk_span_valid_2 l dq1 sz1 dq2 sz2 :
      sz1 = sz2 →
      0 < sz1 →
      chunk_span l dq1 sz1 -∗
      chunk_span l dq2 sz2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝.
    Proof.
      iIntros "% % Hspan1 Hspan2".
      iDestruct (chunk_span_combine with "Hspan1 Hspan2") as "Hspan"; first done.
      iDestruct (chunk_span_valid with "Hspan") as %?; first done.
      iSmash.
    Qed.
    Lemma chunk_span_dfrac_ne l1 dq1 sz1 l2 dq2 sz2 :
      sz1 = sz2 →
      0 < sz1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk_span l1 dq1 sz1 -∗
      chunk_span l2 dq2 sz2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      iIntros "% % % Hspan1 Hspan2" (->).
      iDestruct (chunk_span_valid_2 with "Hspan1 Hspan2") as %?; done.
    Qed.
    Lemma chunk_span_ne l1 sz1 l2 dq2 sz2 :
      sz1 = sz2 →
      0 < sz1 →
      chunk_span l1 (DfracOwn 1) sz1 -∗
      chunk_span l2 dq2 sz2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      intros. iApply chunk_span_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk_span_exclusive l sz1 sz2 :
      sz1 = sz2 →
      0 < sz1 →
      chunk_span l (DfracOwn 1) sz1 -∗
      chunk_span l (DfracOwn 1) sz2 -∗
      False.
    Proof.
      iIntros "% % Hspan1 Hspan2".
      iDestruct (chunk_span_valid_2 with "Hspan1 Hspan2") as %?; done.
    Qed.
    Lemma chunk_span_persist l dq sz :
      chunk_span l dq sz ⊢ |==>
      chunk_span l DfracDiscarded sz.
    Proof.
      iIntros "(%vs & % & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iSmash.
    Qed.
  End chunk_span.

  Lemma chunk_make_spec sz v :
    (0 ≤ sz)%Z →
    {{{ True }}}
      chunk_make #sz v
    {{{ l,
      RET #l;
      chunk_model l (DfracOwn 1) (replicate (Z.to_nat sz) v) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    wp_rec. wp_pures.
    case_bool_decide; wp_pures.
    - setoid_rewrite decide_True; [| done..].
      wp_apply (wp_allocN with "[//]"); first done. iIntros "%l (H↦ & Hmeta)".
      destruct (Z.to_nat sz) eqn:Heq; first lia. iDestruct "Hmeta" as "(Hmeta & _)". rewrite Loc.add_0.
      iApply "HΦ". rewrite /array. iFrame.
    - assert (sz = 0) as -> by lia. iSmash.
  Qed.

  #[local] Lemma chunk_init_aux_spec i vs_done k Ψ l sz fn :
    i = length vs_done →
    sz = Z.of_nat (i + k) →
    {{{
      chunk_model (l +ₗ i) (DfracOwn 1) (replicate k #()) ∗
      Ψ vs_done ∗
      [∗ list] j ∈ seq i k, ∀ vs_done,
        ⌜j = length vs_done⌝ -∗
        Ψ vs_done -∗
        WP fn #(j : nat) {{ v, Ψ (vs_done ++ [v]) }}
    }}}
      chunk_init_aux #l #sz fn #i
    {{{ vs,
      RET #() ;
      ⌜length vs = k⌝ ∗
      chunk_model (l +ₗ i) (DfracOwn 1) vs ∗
      Ψ (vs_done ++ vs)
    }}}.
  Proof.
    iIntros "%Hi %Hk %Φ (Hmodel & HΨ & Hfn) HΦ".
    iInduction k as [| k] "IH" forall (i vs_done Hi Hk); simplify; wp_rec; wp_pures.
    { rewrite bool_decide_eq_true_2; last (repeat f_equal; lia).
      wp_pures.
      iApply ("HΦ" $! []). rewrite right_id. naive_solver.
    }
    iDestruct (chunk_model_cons with "Hmodel") as "(H↦ & Hmodel)".
    rewrite Loc.add_assoc Z.add_1_r -Nat2Z.inj_succ.
    iDestruct "Hfn" as "[Hfn Hfn']".
    rewrite bool_decide_eq_false_2; last naive_solver lia.
    wp_smart_apply (wp_wand with "(Hfn [//] HΨ)"). iIntros "%v HΨ".
    wp_store. wp_pures.
    rewrite Z.add_1_r -Nat2Z.inj_succ.
    iApply ("IH" $! _ (vs_done ++ [v]) with "[] [] Hmodel HΨ Hfn'").
    { rewrite app_length /=. auto with lia. }
    { auto with lia. }
    iIntros "!> %vs". iIntros "(<- & Hmodel & HΨ')".
    iApply ("HΦ" $! (v :: vs)).
    iSplit; first iSmash. iSplitL "H↦ Hmodel".
    - iFrame. rewrite Loc.add_assoc Z.add_1_r -Nat2Z.inj_succ //.
    - rewrite -assoc //.
  Qed.
  Lemma chunk_init_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ [] ∗
      [∗ list] i ∈ seq 0 (Z.to_nat sz), ∀ vs_done,
        ⌜i = length vs_done⌝ -∗
        Ψ vs_done -∗
        WP fn #(i : nat) {{ v, Ψ (vs_done ++ [v]) }}
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      Ψ vs ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_make_spec with "[//]"); first done. iIntros "%l (Hmodel & Hmeta)".
    wp_smart_apply (chunk_init_aux_spec 0 [] with "[Hmodel HΨ $Hfn] [Hmeta HΦ]"); [done | lia | |].
    { iFrame. rewrite Loc.add_0 //. }
    iIntros "!> %vs (%Hsz & Hmodel & HΨ)".
    wp_pures.
    iApply ("HΦ" $! _ vs). rewrite Loc.add_0. iSmash.
  Qed.
  Lemma chunk_init_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ [] ∗
      ∀ i vs_done,
      {{{ ⌜i = length vs_done ∧ i < Z.to_nat sz⌝ ∗ Ψ vs_done }}}
        fn #i
      {{{ v, RET v; Ψ (vs_done ++ [v]) }}}
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      Ψ vs ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ (HΨ & #Hfn) HΦ".
    wp_apply (chunk_init_spec Ψ with "[$HΨ]"); try done.
    iApply big_sepL_intro. iIntros "!> %i %_i %H_i %vs_done % HΨ". apply lookup_seq in H_i as (-> & ?).
    iApply ("Hfn" with "[$HΨ]"); iSmash.
  Qed.
  Lemma chunk_init_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #(i : nat) {{ Ψ i }}
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      ([∗ list] i ↦ v ∈ vs, Ψ i v) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ Hfn HΦ".
    set (Ψ' vs := ([∗ list] i ↦ v ∈ vs, Ψ i v)%I).
    wp_apply (chunk_init_spec Ψ' with "[Hfn]"); try done.
    iSplit; first rewrite /Ψ' //.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v % Hfn %vs_done -> HΨ'".
    iApply (wp_wand with "Hfn"). iIntros "%v HΨ". iFrame. iSplitL; last iSmash.
    rewrite right_id //.
  Qed.
  Lemma chunk_init_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ∀ i,
      {{{ ⌜i < Z.to_nat sz⌝ }}}
        fn #i
      {{{ v, RET v; Ψ i v }}}
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      ([∗ list] i ↦ v ∈ vs, Ψ i v) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ #Hfn HΦ".
    wp_apply chunk_init_spec_disentangled; try done.
    iApply big_sepL_intro. iIntros "!> %i %_i %Hlookup".
    apply lookup_seq in Hlookup as (-> & ?).
    iApply ("Hfn" with "[//]"). iSmash.
  Qed.

  Lemma chunk_get_spec v l (i : Z) dq vs E :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      chunk_model l dq vs
    }}}
      !#(l +ₗ i) @ E
    {{{
      RET v;
      chunk_model l dq vs
    }}}.
  Proof.
    iIntros "% % %Φ Hmodel HΦ".
    iDestruct (chunk_model_lookup_acc with "Hmodel") as "(H↦ & Hmodel)"; first done.
    rewrite (Z2Nat.id i) //. wp_load.
    iSmash.
  Qed.

  Lemma chunk_set_spec l (i : Z) vs v E :
    (0 ≤ i < length vs)%Z →
    {{{
      chunk_model l (DfracOwn 1) vs
    }}}
      #(l +ₗ i) <- v @ E
    {{{
      RET #();
      chunk_model l (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "% %Φ Hmodel HΦ".
    iDestruct (chunk_model_update with "Hmodel") as "(H↦ & Hmodel)".
    { destruct (nth_lookup_or_length vs (Z.to_nat i) inhabitant); [done | lia]. }
    rewrite (Z2Nat.id i); last lia. wp_store.
    iSmash.
  Qed.

  #[local] Lemma chunk_foldli_aux_spec i vs_done vs_todo Ψ l dq sz acc fn :
    i = length vs_done →
    (sz = i + length vs_todo)%Z →
    {{{
      chunk_model (l +ₗ i) dq vs_todo ∗
      Ψ vs_done acc ∗
      [∗ list] j ↦ v ∈ vs_todo, ∀ acc,
        Ψ (vs_done ++ take j vs_todo) acc -∗
        WP fn acc #(i + j) (v : val) {{ acc', Ψ (vs_done ++ take j vs_todo ++ [v]) acc' }}
    }}}
      chunk_foldli_aux #l #sz acc fn #i
    {{{ acc',
      RET acc';
      chunk_model (l +ₗ i) dq vs_todo ∗
      Ψ (vs_done ++ vs_todo) acc'
    }}}.
  Proof.
    iIntros "%Hi %Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    iInduction vs_todo as [| v vs_todo] "IH" forall (i vs_done Hi Hsz acc); simplify; wp_rec; wp_pures.
    { rewrite bool_decide_eq_true_2; last (repeat f_equal; lia).
      wp_pures.
      iApply "HΦ". iFrame. rewrite right_id //.
    }
    iDestruct "Hmodel" as "(H↦ & Hmodel)". rewrite Loc.add_0.
    iDestruct "Hfn" as "(Hfn & Hfn')". rewrite right_id Z.add_0_r.
    rewrite bool_decide_eq_false_2; last naive_solver lia.
    wp_pures. wp_load.
    wp_bind (fn _ _ _). iApply (wp_wand with "(Hfn [HΨ])"); first by list_simplifier. iIntros "%acc' HΨ".
    rewrite Z.add_1_r -Nat2Z.inj_succ.
    wp_apply ("IH" $! _ (vs_done ++ [v]) with "[] [] [Hmodel] HΨ [Hfn']").
    { rewrite app_length /=. auto with lia. }
    { auto with lia. }
    { rewrite /chunk_model.
      setoid_rewrite Loc.add_assoc.
      setoid_rewrite <- Nat2Z.inj_add.
      setoid_rewrite Nat.add_succ_r.
      iSmash.
    } {
      setoid_rewrite <- (assoc (++) vs_done [v]).
      setoid_rewrite <- Nat2Z.inj_add.
      setoid_rewrite Nat.add_succ_r.
      iSmash.
    }
    iIntros "%acc'' (Hmodel & HΨ)".
    iApply "HΦ". rewrite -(assoc (++) vs_done [v]). iFrame.
    rewrite Loc.add_assoc Z.add_1_r -Nat2Z.inj_succ //.
  Qed.
  Lemma chunk_foldli_spec Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] acc ∗
      [∗ list] i ↦ v ∈ vs, ∀ acc,
        Ψ (take i vs) acc -∗
        WP fn acc #i (v : val) {{ acc', Ψ (take i vs ++ [v]) acc' }}
    }}}
      chunk_foldli #l #sz acc fn
    {{{ acc',
      RET acc';
      chunk_model l dq vs ∗
      Ψ vs acc'
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_aux_spec 0 [] vs Ψ with "[Hmodel $HΨ $Hfn]"); [done | lia | |].
    { rewrite Loc.add_0 //. }
    iIntros "%acc' (Hmodel & HΨ)". rewrite Loc.add_0. iSmash.
  Qed.
  Lemma chunk_foldli_spec' Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] acc ∗
      ∀ acc i v,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) acc }}}
        fn acc #i v
      {{{ acc', RET acc'; Ψ (take i vs ++ [v]) acc' }}}
    }}}
      chunk_foldli #l #sz acc fn
    {{{ acc',
      RET acc';
      chunk_model l dq vs ∗
      Ψ vs acc'
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_apply (chunk_foldli_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v % %acc HΨ".
    wp_apply ("Hfn" with "[$HΨ //]").
    iSmash.
  Qed.

  Lemma chunk_foldl_spec Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] acc ∗
      [∗ list] i ↦ v ∈ vs, ∀ acc,
        Ψ (take i vs) acc -∗
        WP fn acc (v : val) {{ acc', Ψ (take i vs ++ [v]) acc' }}
    }}}
      chunk_foldl #l #sz acc fn
    {{{ acc',
      RET acc';
      chunk_model l dq vs ∗
      Ψ vs acc'
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply (big_sepL_mono with "Hfn").
    iSmash.
  Qed.
  Lemma chunk_foldl_spec' Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] acc ∗
      ∀ i v acc,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) acc }}}
        fn acc v
      {{{ acc', RET acc'; Ψ (take i vs ++ [v]) acc' }}}
    }}}
      chunk_foldl #l #sz acc fn
    {{{ acc',
      RET acc';
      chunk_model l dq vs ∗
      Ψ vs acc'
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_apply (chunk_foldl_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v % %acc HΨ".
    wp_apply ("Hfn" with "[$HΨ //]").
    iSmash.
  Qed.

  #[local] Lemma chunk_foldri_aux_spec i vs_todo vs_done Ψ l dq acc fn :
    i = length vs_todo →
    {{{
      chunk_model l dq vs_todo ∗
      Ψ acc vs_done ∗
      [∗ list] j ↦ v ∈ vs_todo, ∀ acc,
        Ψ acc (drop (S j) vs_todo ++ vs_done) -∗
        WP fn #j (v : val) acc {{ acc', Ψ acc' (v :: drop (S j) vs_todo ++ vs_done) }}
    }}}
      chunk_foldri_aux #l fn acc #i
    {{{ acc',
      RET acc';
      chunk_model l dq vs_todo ∗
      Ψ acc' (vs_todo ++ vs_done)
    }}}.
  Proof.
    iIntros "%Hi %Φ (Hmodel & HΨ & Hfn) HΦ".
    iInduction vs_todo as [| v vs_todo] "IH" using rev_ind forall (i vs_done Hi acc); simplify; wp_rec; wp_pures.
    { iApply ("HΦ" with "[$Hmodel $HΨ]"). }
    iDestruct "Hmodel" as "(Hmodel & H↦ & _)". iEval (rewrite right_id) in "H↦".
    iDestruct "Hfn" as "(Hfn' & Hfn & _)".
    iEval (
      rewrite
        right_id
        -(right_id [] (++) (vs_todo ++ [v])) drop_app_alt /=;
          last (rewrite app_length /=; lia)
    ) in "Hfn".
    rewrite app_length bool_decide_eq_false_2; last naive_solver lia.
    wp_pures.
    rewrite Nat.add_1_r Nat2Z.inj_succ Z.sub_1_r Z.pred_succ. wp_load.
    wp_bind (fn _ _ _). iApply (wp_wand with "(Hfn HΨ)").
    iIntros "%acc' HΨ".
    wp_apply ("IH" $! _ (v :: vs_done) with "[//] Hmodel HΨ [Hfn']").
    { iApply (big_sepL_mono with "Hfn'"). clear. iIntros "%i %w %Hlookup Hfn %acc HΨ".
      rewrite drop_app_le; last first.
      { apply lookup_lt_Some in Hlookup. lia. }
      rewrite -(assoc (++)) /=. iSmash.
    }
    iIntros "%acc'' (Hmodel & HΨ)".
    iApply "HΦ". rewrite -(assoc (++) vs_todo [v]). iFrame. iSplitL; last iSmash.
    rewrite right_id //.
  Qed.
  Lemma chunk_foldri_spec Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ acc [] ∗
      [∗ list] i ↦ v ∈ vs, ∀ acc,
        Ψ acc (drop (S i) vs) -∗
        WP fn #i (v : val) acc {{ acc', Ψ acc' (v :: drop (S i) vs) }}
    }}}
      chunk_foldri #l #sz fn acc
    {{{ acc',
      RET acc';
      chunk_model l dq vs ∗
      Ψ acc' vs
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & Hfn) HΦ".
    Z_to_nat sz. simplify.
    wp_rec.
    wp_smart_apply (chunk_foldri_aux_spec _ vs [] Ψ with "[$Hmodel $HΨ Hfn]"); first done.
    { iApply (big_sepL_impl with "Hfn").
      iModIntro. iIntros. rewrite right_id. iSmash.
    }
    iIntros "%acc' (Hmodel & HΨ)".
    iApply "HΦ". iFrame. rewrite right_id //.
  Qed.
  Lemma chunk_foldri_spec' Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ acc [] ∗
      ∀ acc i v,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ acc (drop (S i) vs) }}}
        fn #i v acc
      {{{ acc', RET acc'; Ψ acc' (v :: drop (S i) vs) }}}
    }}}
      chunk_foldri #l #sz fn acc
    {{{ acc',
      RET acc';
      chunk_model l dq vs ∗
      Ψ acc' vs
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_apply (chunk_foldri_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v % %acc HΨ".
    wp_apply ("Hfn" with "[$HΨ //]").
    iSmash.
  Qed.

  Lemma chunk_foldr_spec Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ acc [] ∗
      [∗ list] i ↦ v ∈ vs, ∀ acc,
        Ψ acc (drop (S i) vs) -∗
        WP fn (v : val) acc {{ acc', Ψ acc' (v :: drop (S i) vs) }}
    }}}
      chunk_foldr #l #sz fn acc
    {{{ acc',
      RET acc';
      chunk_model l dq vs ∗
      Ψ acc' vs
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldri_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply (big_sepL_mono with "Hfn").
    iSmash.
  Qed.
  Lemma chunk_foldr_spec' Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ acc [] ∗
      ∀ i v acc,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ acc (drop (S i) vs) }}}
        fn v acc
      {{{ acc', RET acc'; Ψ acc' (v :: drop (S i) vs) }}}
    }}}
      chunk_foldr #l #sz fn acc
    {{{ acc',
      RET acc';
      chunk_model l dq vs ∗
      Ψ acc' vs
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_apply (chunk_foldr_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v % %acc HΨ".
    wp_apply ("Hfn" with "[$HΨ //]").
    iSmash.
  Qed.

  Lemma chunk_iteri_spec Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] ∗
      [∗ list] i ↦ v ∈ vs,
        Ψ (take i vs) -∗
        WP fn #i (v : val) {{ _, Ψ (take i vs ++ [v]) }}
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_spec (λ vs acc, ⌜acc = #()⌝ ∗ Ψ vs)%I with "[$Hmodel $HΨ Hfn]"); try iSmash+.
    iSplit; first iSmash.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v % Hfn %acc (-> & HΨ)".
    iSmash.
  Qed.
  Lemma chunk_iteri_spec' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] ∗
      ∀ i v,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) }}}
        fn #i v
      {{{ w, RET w; Ψ (take i vs ++ [v]) }}}
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_apply (chunk_iteri_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v % HΨ".
    wp_apply ("Hfn" with "[$HΨ //]").
    iSmash.
  Qed.
  Lemma chunk_iteri_spec_disentangled Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      [∗ list] i ↦ v ∈ vs,
        WP fn #i (v : val) {{ _, Ψ i v }}
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      [∗ list] i ↦ v ∈ vs, Ψ i v
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & Hfn) HΦ".
    set (Ψ' vs := ([∗ list] i ↦ v ∈ vs, Ψ i v)%I).
    wp_apply (chunk_iteri_spec Ψ' with "[$Hmodel Hfn]"); try done.
    iSplit; first rewrite /Ψ' //.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v %Hlookup Hfn HΨ'".
    iApply (wp_wand with "Hfn"). iIntros "%w HΨ". iFrame. iSplitL; last iSmash.
    rewrite right_id take_length_le //. apply lookup_lt_Some in Hlookup. lia.
  Qed.
  Lemma chunk_iteri_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ∀ i v,
      {{{ ⌜vs !! i = Some v⌝ }}}
        fn #i v
      {{{ w, RET w; Ψ i v }}}
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      [∗ list] i ↦ v ∈ vs, Ψ i v
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & #Hfn) HΦ".
    wp_apply (chunk_iteri_spec_disentangled with "[$Hmodel]"); try done.
    iApply big_sepL_intro. iIntros "!> %i %v %".
    iApply ("Hfn" with "[//]").
    iSmash.
  Qed.

  Lemma chunk_iter_spec Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] ∗
      [∗ list] i ↦ v ∈ vs,
        Ψ (take i vs) -∗
        WP fn (v : val) {{ _, Ψ (take i vs ++ [v]) }}
    }}}
      chunk_iter #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply (big_sepL_mono with "Hfn").
    iSmash.
  Qed.
  Lemma chunk_iter_spec' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] ∗
      ∀ i v,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) }}}
        fn v
      {{{ w, RET w; Ψ (take i vs ++ [v]) }}}
    }}}
      chunk_iter #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_apply (chunk_iter_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v % HΨ".
    wp_apply ("Hfn" with "[$HΨ //]").
    iSmash.
  Qed.
  Lemma chunk_iter_spec_disentangled Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      [∗ list] v ∈ vs,
        WP fn (v : val) {{ _, Ψ v }}
    }}}
      chunk_iter #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      [∗ list] v ∈ vs, Ψ v
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & Hfn) HΦ".
    set (Ψ' vs := ([∗ list] v ∈ vs, Ψ v)%I).
    wp_apply (chunk_iter_spec Ψ' with "[$Hmodel Hfn]"); try done.
    iSplit; first rewrite /Ψ' //.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v % Hfn HΨ'".
    iApply (wp_wand with "Hfn"). iIntros "%w HΨ".
    iFrame. iSmash.
  Qed.
  Lemma chunk_iter_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ∀ v,
      {{{ ⌜v ∈ vs⌝ }}}
        fn v
      {{{ w, RET w; Ψ v }}}
    }}}
      chunk_iter #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      [∗ list] v ∈ vs, Ψ v
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & #Hfn) HΦ".
    wp_apply (chunk_iter_spec_disentangled with "[$Hmodel]"); try done.
    iApply big_sepL_intro. iIntros "!> %i %v %".
    iApply "Hfn"; last iSmash.
    rewrite elem_of_list_lookup. iSmash.
  Qed.

  Lemma chunk_mapi_spec Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] [] ∗
      [∗ list] i ↦ v ∈ vs, ∀ ws,
        ⌜length ws = i⌝ -∗
        Ψ (take i vs) ws -∗
        WP fn #i (v : val) {{ w, Ψ (take i vs ++ [v]) (ws ++ [w]) }}
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    pose Ψ' ws := (
      let vs := take (length ws) vs in
      Ψ vs ws ∗ chunk_model l dq vs
    )%I.
    wp_smart_apply (chunk_init_spec Ψ' with "[Hmodel $HΨ Hfn]"); first lia.
    { iSplit; first rewrite /chunk_model take_0 //.
      Z_to_nat sz. rewrite Nat2Z.id.
      iApply (big_sepL_seq_index vs); first naive_solver.
      iDestruct (big_sepL_sep_2 with "Hmodel Hfn") as "H".
      iApply (big_sepL_mono with "H"). iIntros "%i %v %Hlookup (H↦ & Hfn) %ws -> (HΨ & Hmodel)".
      wp_pures. wp_load.
      iApply (wp_wand with "(Hfn [//] HΨ)"). iIntros "%w HΨ".
      rewrite /Ψ' app_length /= Nat.add_1_r (take_S_r _ _ v) //.
      iFrame. iSplitL; last iSmash. rewrite right_id take_length_le //.
      apply lookup_lt_Some in Hlookup. lia.
    }
    iIntros "%l' %ws (%Hws & Hmodel' & (HΨ & Hmodel) & Hmeta)".
    rewrite Hws Hsz Nat2Z.id firstn_all. iSmash.
  Qed.
  Lemma chunk_mapi_spec' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] [] ∗
      ∀ i v ws,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) ws }}}
        fn #i v
      {{{ w, RET w; Ψ (take i vs ++ [v]) (ws ++ [w]) }}}
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_apply (chunk_mapi_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v % %ws % HΨ".
    wp_apply ("Hfn" with "[$HΨ //]").
    iSmash.
  Qed.
  Lemma chunk_mapi_spec_disentangled Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      [∗ list] i ↦ v ∈ vs,
        WP fn #i (v : val) {{ w, Ψ i v w }}
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ([∗ list] i ↦ v; w ∈ vs; ws, Ψ i v w) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & Hfn) HΦ".
    set (Ψ' vs ws := ([∗ list] i ↦ v; w ∈ vs; ws, Ψ i v w)%I).
    wp_apply (chunk_mapi_spec Ψ' with "[$Hmodel Hfn]"); try done.
    iSplit; first rewrite /Ψ' //.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v %Hlookup Hfn %ws % HΨ'".
    iApply (wp_wand with "Hfn"). iIntros "%w HΨ". iFrame. iSplitL; last iSmash.
    rewrite right_id take_length_le //. apply lookup_lt_Some in Hlookup. lia.
  Qed.
  Lemma chunk_mapi_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ∀ i v,
      {{{ ⌜vs !! i = Some v⌝ }}}
        fn #i v
      {{{ w, RET w; Ψ i v w }}}
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ([∗ list] i ↦ v; w ∈ vs; ws, Ψ i v w) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & #Hfn) HΦ".
    wp_apply (chunk_mapi_spec_disentangled Ψ with "[$Hmodel Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v %".
    iApply ("Hfn" with "[//]").
    iSmash.
  Qed.

  Lemma chunk_map_spec Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] [] ∗
      [∗ list] i ↦ v ∈ vs, ∀ ws,
        Ψ (take i vs) ws -∗
        WP fn (v : val) {{ w, Ψ (take i vs ++ [v]) (ws ++ [w]) }}
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply (big_sepL_mono with "Hfn").
    iSmash.
  Qed.
  Lemma chunk_map_spec' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ [] [] ∗
      ∀ i v ws,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) ws }}}
        fn v
      {{{ w, RET w; Ψ (take i vs ++ [v]) (ws ++ [w]) }}}
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_apply (chunk_map_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v % %w HΨ".
    wp_apply ("Hfn" with "[$HΨ //]").
    iSmash.
  Qed.
  Lemma chunk_map_spec_disentangled Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      [∗ list] v ∈ vs,
        WP fn (v : val) {{ Ψ v }}
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ([∗ list] v; w ∈ vs; ws, Ψ v w) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & Hfn) HΦ".
    set (Ψ' vs ws := ([∗ list] v; w ∈ vs; ws, Ψ v w)%I).
    wp_apply (chunk_map_spec Ψ' with "[$Hmodel Hfn]"); try done.
    iSplit; first rewrite /Ψ' //.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v % Hfn %ws HΨ'".
    iApply (wp_wand with "Hfn"). iIntros "%w HΨ".
    iFrame. iSmash.
  Qed.
  Lemma chunk_map_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ∀ v,
      {{{ ⌜v ∈ vs⌝ }}}
        fn v
      {{{ w, RET w; Ψ v w }}}
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ([∗ list] v; w ∈ vs; ws, Ψ v w) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "% %Φ (Hmodel & #Hfn) HΦ".
    wp_apply (chunk_map_spec_disentangled Ψ with "[$Hmodel Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v %".
    iApply "Hfn"; last iSmash.
    rewrite elem_of_list_lookup. iSmash.
  Qed.

  Lemma chunk_copy_spec l dq vs (sz : Z) l' vs' :
    sz = length vs →
    sz = length vs' →
    {{{
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) vs'
    }}}
      chunk_copy #l #sz #l'
    {{{
      RET #();
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) vs
    }}}.
  Proof.
    iIntros (-> Hsz%(inj _)) "%Φ (Hmodel & Hmodel') HΦ".
    wp_rec.
    set (Ψ vs := chunk_model l' (DfracOwn 1) (vs ++ drop (length vs) vs')).
    wp_smart_apply (chunk_iteri_spec' Ψ with "[$Hmodel Hmodel']"); first done; last first.
    { iIntros "(Hmodel & HΨ)".
      iApply "HΦ". iFrame. rewrite /Ψ Hsz drop_all right_id //.
    }
    iFrame. clear- Hsz. iIntros "%i %v !> %Φ (%Hlookup & HΨ) HΦ".
    pose proof Hlookup as Hi%lookup_lt_Some.
    wp_smart_apply (chunk_set_spec with "HΨ").
    { rewrite app_length take_length_le; last lia. rewrite drop_length. lia. }
    iIntros "Hmodel'".
    iApply "HΦ".
    rewrite /Ψ Nat2Z.id app_length -assoc Nat.add_1_r insert_app_r_alt take_length_le; [| lia..].
    rewrite Nat.sub_diag insert_take_drop.
    - rewrite drop_drop Nat.add_1_r //.
    - rewrite drop_length. lia.
  Qed.

  Lemma chunk_grow_spec l dq vs (sz : Z) sz' v :
    sz = length vs →
    (sz ≤ sz')%Z →
    {{{
      chunk_model l dq vs
    }}}
      chunk_grow #l #sz #sz' v
    {{{ l',
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) (vs ++ replicate (Z.to_nat (sz' - sz)) v)
    }}}.
  Proof.
    iIntros "%Hsz %Hsz' %Φ Hmodel HΦ".
    Z_to_nat sz. Z_to_nat sz'.
    destruct (Nat.le_exists_sub sz sz') as (dsz & Heq & _); first lia.
    rewrite (comm Nat.add) in Heq. subst sz'.
    wp_rec.
    wp_smart_apply (chunk_make_spec with "[//]"); first lia. iIntros "%l' (Hmodel' & _)".
    rewrite Nat2Z.id replicate_add.
    iDestruct (chunk_model_app_2 with "Hmodel'") as "(Hmodel'1 & Hmodel'2)"; first done.
    wp_smart_apply (chunk_copy_spec with "[$Hmodel $Hmodel'1]"); first done.
    { rewrite replicate_length. lia. }
    iIntros "(Hmodel & Hmodel'1)".
    rewrite -Nat2Z.inj_sub; last lia. rewrite Nat2Z.id Nat.sub_add' replicate_length Hsz.
    iDestruct (chunk_model_app_1 with "Hmodel'1 Hmodel'2") as "Hmodel'"; first done.
    iSmash.
  Qed.

  Lemma chunk_shrink_spec l dq vs (sz : Z) sz' :
    sz = length vs →
    (0 ≤ sz' ≤ sz)%Z →
    {{{
      chunk_model l dq vs
    }}}
      chunk_shrink #l #sz #sz'
    {{{ l',
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) (take (Z.to_nat sz') vs)
    }}}.
  Proof.
    iIntros "%Hsz %Hsz' %Φ Hmodel HΦ".
    Z_to_nat sz. Z_to_nat sz'.
    destruct (Nat.le_exists_sub sz' sz) as (dsz & Heq & _); first lia.
    rewrite (comm Nat.add) in Heq. subst sz.
    wp_rec.
    wp_smart_apply (chunk_make_spec with "[//]"); first lia. iIntros "%l' (Hmodel' & _)".
    rewrite Nat2Z.id -{1}(take_drop sz' vs).
    iDestruct (chunk_model_app_2 with "Hmodel") as "(Hmodel1 & Hmodel2)"; first done.
    wp_smart_apply (chunk_copy_spec with "[$Hmodel1 $Hmodel']").
    { rewrite take_length_le; lia. }
    { rewrite replicate_length. lia. }
    iIntros "(Hmodel1 & Hmodel')".
    rewrite take_length_le; last lia.
    iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel".
    { rewrite take_length_le; lia. }
    rewrite take_drop.
    iSmash.
  Qed.

  Lemma chunk_clone_spec l dq vs (sz : Z) :
    sz = length vs →
    {{{
      chunk_model l dq vs
    }}}
      chunk_clone #l #sz
    {{{ l',
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (chunk_shrink_spec with "Hmodel"); [lia.. |].
    iIntros "%l' (Hmodel & Hmodel')".
    iApply "HΦ".
    rewrite Hsz Nat2Z.id firstn_all. iSmash.
  Qed.
End heapGS.

#[global] Opaque chunk_make.
#[global] Opaque chunk_init.
#[global] Opaque chunk_foldli.
#[global] Opaque chunk_foldl.
#[global] Opaque chunk_foldri.
#[global] Opaque chunk_foldr.
#[global] Opaque chunk_iteri.
#[global] Opaque chunk_iter.
#[global] Opaque chunk_mapi.
#[global] Opaque chunk_map.
#[global] Opaque chunk_copy.
#[global] Opaque chunk_grow.
#[global] Opaque chunk_shrink.
#[global] Opaque chunk_clone.

#[global] Opaque chunk_model.
#[global] Opaque chunk_span.
