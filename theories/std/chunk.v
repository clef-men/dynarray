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
  Implicit Types vs vs_done vs_todo ws : list val.

  Definition chunk_make : val :=
    λ: "sz" "v",
      if: #0 < "sz" then (
        AllocN "sz" "v"
) else (
        #(inhabitant : loc)
      ).

  #[local] Definition chunk_foldli_aux : val :=
    rec: "chunk_foldli_aux" "t" "sz" "acc" "fn" "i" :=
      if: "i" = "sz" then (
        "acc"
      ) else (
        "chunk_foldli_aux" "t" "sz" ("fn" "acc" "i" !("t" +ₗ "i")) "fn" (#1 + "i")
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

  Definition chunk_applyi : val :=
    λ: "t" "sz" "fn",
      chunk_iteri "t" "sz" (λ: "i" "v", "t" +ₗ "i" <- "fn" "i" "v").
  Definition chunk_apply : val :=
    λ: "t" "sz" "fn",
      chunk_applyi "t" "sz" (λ: <> "v", "fn" "v").

  Definition chunk_initi : val :=
    λ: "sz" "fn",
      let: "t" := chunk_make "sz" #() in
      chunk_applyi "t" "sz" (λ: "i" <>, "fn" "i") ;;
      "t".
  Definition chunk_init : val :=
    λ: "sz" "fn",
      chunk_initi "sz" (λ: <>, "fn" #()).

  Definition chunk_mapi : val :=
    λ: "t" "sz" "fn",
      chunk_initi "sz" (λ: "i", "fn" "i" !("t" +ₗ "i")).
  Definition chunk_map : val :=
    λ: "t" "sz" "fn",
      chunk_mapi "t" "sz" (λ: <> "v", "fn" "v").

  Definition chunk_copy : val :=
    λ: "t" "sz" "t'",
      chunk_iteri "t" "sz" (λ: "i" "v", "t'" +ₗ "i" <- "v").

  Definition chunk_resize : val :=
    λ: "t" "sz" "sz'" "n" "v",
      let: "t'" := chunk_make "sz'" "v" in
      chunk_copy "t" "n" "t'" ;;
      "t'".
  Definition chunk_grow : val :=
    λ: "t" "sz" "sz'" "v",
      chunk_resize "t" "sz" "sz'" "sz" "v".
  Definition chunk_shrink : val :=
    λ: "t" "sz" "sz'",
      chunk_resize "t" "sz" "sz'" "sz'" (inhabitant : val).

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
        ⌜vs1 = vs2⌝ ∗
        chunk_model l (dq1 ⋅ dq2) vs1.
    Proof.
      iInduction vs1 as [| v1 vs1] "IH" forall (l vs2); iIntros "% Hmodel1 Hmodel2".
      - rewrite (nil_length_inv vs2); last done. naive_solver.
      - destruct vs2 as [| v2 vs2]; first iSmash.
        iDestruct (chunk_model_cons_2 with "Hmodel1") as "(H↦1 & Hmodel1)".
        iDestruct (chunk_model_cons_2 with "Hmodel2") as "(H↦2 & Hmodel2)".
        iDestruct (mapsto_combine with "H↦1 H↦2") as "(H↦ & ->)".
        iDestruct ("IH" with "[] Hmodel1 Hmodel2") as "(-> & Hmodel)"; first iSmash. iSplit; first iSmash.
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
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(-> & Hmodel)"; first done.
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
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(-> & _)"; first done.
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
      intros.
      iApply chunk_model_dfrac_ne; [done.. | intros []%(exclusive_l _)].
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
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)"; first naive_solver.
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
      intros.
      iApply chunk_span_dfrac_ne; [done.. | intros []%(exclusive_l _)].
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

  Notation chunk_au_load l i Φ := (
    AU << ∃∃ dq v,
      (l +ₗ i) ↦{dq} v
    >> @ ⊤, ∅ <<
      (l +ₗ i) ↦{dq} v,
    COMM
      Φ v
    >>
  )%I.
  Notation chunk_au_store l i v P := (
    AU << ∃∃ v',
      (l +ₗ i) ↦ v'
    >> @ ⊤, ∅ <<
      (l +ₗ i) ↦ v,
    COMM
      P
    >>
  )%I.

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

  #[local] Lemma chunk_foldli_aux_spec i vs Ψ l (sz : Z) acc fn :
    (i ≤ sz)%Z →
    i = length vs →
    {{{
      Ψ i vs None acc ∗
      □ (
        ∀ i vs acc,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs None acc -∗
        chunk_au_load l i (λ v,
          Ψ i vs (Some v) acc
        )
      ) ∗
      □ (
        ∀ i vs v acc,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs (Some v) acc -∗
        WP fn acc #i v {{ acc,
          Ψ (S i) (vs ++ [v]) None acc
        }}
      )
    }}}
      chunk_foldli_aux #l #sz acc fn #i
    {{{ vs' acc,
      RET acc;
      ⌜(length vs + length vs')%nat = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) (vs ++ vs') None acc
    }}}.
  Proof.
    iIntros "%Hi1 %Hi2 %Φ (HΨ & #Hau & #Hfn) HΦ".
    Z_to_nat sz. rewrite Nat2Z.id. remember (sz - i) as j eqn:Hj.
    iInduction j as [| j] "IH" forall (i vs acc Hi1 Hi2 Hj);
      wp_rec; wp_pures.
    - rewrite bool_decide_eq_true_2; last (repeat f_equal; lia). wp_pures.
      iApply ("HΦ" $! []).
      rewrite !right_id. assert (sz = i) by lia. iSmash.
    - rewrite bool_decide_eq_false_2; last naive_solver lia. wp_pures.
      wp_bind (!_)%E.
      iMod ("Hau" $! i with "[] HΨ") as "(%dq & %v & H↦ & _ & HΨ)"; first iSmash.
      wp_load.
      iMod ("HΨ" with "H↦") as "HΨ". iModIntro.
      wp_apply (wp_wand with "(Hfn [] HΨ)"); first iSmash. iIntros "%acc' HΨ".
      rewrite Z.add_1_l -Nat2Z.inj_succ.
      wp_apply ("IH" with "[] [] [] HΨ [HΦ]"); rewrite ?app_length; [iSmash.. |].
      clear acc. iIntros "!> %vs' %acc (<- & HΨ)".
      iApply ("HΦ" $! (v :: vs')).
      rewrite -(assoc (++)). iSmash.
  Qed.
  Lemma chunk_foldli_spec_atomic Ψ l sz acc fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] None acc ∗
      □ (
        ∀ i vs acc,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs None acc -∗
        chunk_au_load l i (λ v,
          Ψ i vs (Some v) acc
        )
      ) ∗
      □ (
        ∀ i vs v acc,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs (Some v) acc -∗
        WP fn acc #i v {{ acc,
          Ψ (S i) (vs ++ [v]) None acc
        }}
      )
    }}}
      chunk_foldli #l #sz acc fn
    {{{ vs acc,
      RET acc;
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) vs None acc
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_aux_spec 0 [] Ψ with "[$HΨ] HΦ"); [done.. |].
    auto with iFrame.
  Qed.
  Lemma chunk_foldli_spec Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] acc ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn acc #i v {{ acc,
          Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      chunk_foldli #l #sz acc fn
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs acc
    }}}.
  Proof.
    iIntros "%Hvs %Φ (Hmodel & HΨ & #Hfn) HΦ".
    pose (Ψ' i vs_done o acc := (
      ⌜vs_done = take i vs⌝ ∗
      chunk_model l dq vs ∗
      Ψ i vs_done acc ∗
      ⌜from_option (λ v, v = vs !!! i) True o⌝%I
    )%I).
    wp_apply (chunk_foldli_spec_atomic Ψ' with "[$Hmodel $HΨ]"); last first.
    { clear acc. iIntros "%vs_done %acc (%Hvs_done & (-> & Hmodel & HΨ))".
      rewrite /Ψ' firstn_all2; last lia. iSmash.
    }
    repeat iSplitR.
    - iSmash.
    - clear acc. iIntros "!> %i %vs_done %acc (%Hi & _) (-> & Hmodel & HΨ & _)".
      feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
      iDestruct (chunk_model_lookup_acc with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; iSmash.
    - clear acc. iIntros "!> %i %vs_done %v %acc (%Hi1 & %Hi2) (-> & Hmodel & HΨ & %Hv)". rewrite Hv.
      feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
      wp_apply (wp_wand with "(Hfn [] HΨ)"); first iSmash. clear acc. iIntros "%acc HΨ". iFrame.
      erewrite take_S_r; done.
    - lia.
  Qed.
  Lemma chunk_foldli_spec' Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] acc ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn acc #i v {{ acc,
          Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      chunk_foldli #l #sz acc fn
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs acc
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_done acc := (
      Ψ i vs_done acc ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (chunk_foldli_spec Ψ' with "[$Hmodel HΨ Hfn]"); [done | | iSmash].
    iFrame. clear acc. iIntros "!> %i %v %acc %Hlookup (HΨ & HΞ)".
    erewrite drop_S; last done.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r.
    wp_apply (wp_wand with "(Hfn HΨ)"). clear acc. iIntros "%acc HΨ". iFrame.
    setoid_rewrite Nat.add_succ_r. iSmash.
  Qed.

  Lemma chunk_foldl_spec_atomic Ψ l sz acc fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] None acc ∗
      □ (
        ∀ i vs acc,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs None acc -∗
        chunk_au_load l i (λ v,
          Ψ i vs (Some v) acc
        )
      ) ∗
      □ (
        ∀ i vs v acc,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs (Some v) acc -∗
        WP fn acc v {{ acc,
          Ψ (S i) (vs ++ [v]) None acc
        }}
      )
    }}}
      chunk_foldl #l #sz acc fn
    {{{ vs acc,
      RET acc;
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) vs None acc
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_spec_atomic Ψ with "[$HΨ $Hau] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_foldl_spec Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] acc ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      chunk_foldl #l #sz acc fn
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs acc
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_spec Ψ with "[$Hmodel $HΨ] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_foldl_spec' Ψ l dq vs (sz : Z) acc fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] acc ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      chunk_foldl #l #sz acc fn
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs acc
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldli_spec' Ψ with "[$Hmodel $HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.

  #[local] Lemma chunk_foldri_aux_spec sz i vs Ψ l fn acc :
    i + length vs = sz →
    {{{
      Ψ i acc None vs ∗
      □ (
        ∀ i acc vs,
        ⌜(S i + length vs)%nat = sz⌝ -∗
        Ψ (S i) acc None vs -∗
        chunk_au_load l i (λ v,
          Ψ (S i) acc (Some v) vs
        )
      ) ∗
      □ (
        ∀ i v acc vs,
        ⌜(S i + length vs)%nat = sz⌝ -∗
        Ψ (S i) acc (Some v) vs -∗
        WP fn #i v acc {{ acc,
          Ψ i acc None (v :: vs)
        }}
      )
    }}}
      chunk_foldri_aux #l fn acc #i
    {{{ acc vs',
      RET acc;
      ⌜(length vs' + length vs)%nat = sz⌝ ∗
      Ψ 0 acc None (vs' ++ vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (HΨ & #Hau & #Hfn) HΦ".
    iInduction i as [| i] "IH" forall (vs acc Hi);
      wp_rec; wp_pures.
    - iApply ("HΦ" $! _ []).
      iSmash.
    - wp_bind (!_)%E.
      iMod ("Hau" $! i with "[] HΨ") as "(%dq & %v & H↦ & _ & HΨ)"; first iSmash.
      rewrite Z.sub_1_r -Nat2Z.inj_pred /=; last lia. wp_load.
      iMod ("HΨ" with "H↦") as "HΨ". iModIntro.
      wp_apply (wp_wand with "(Hfn [] HΨ)"); first iSmash. iIntros "%acc' HΨ".
      wp_apply ("IH" with "[] HΨ [HΦ]"); rewrite ?app_length; [iSmash.. |]. clear acc. iIntros "!> %acc %vs' (<- & HΨ)".
      iApply ("HΦ" $! _ (vs' ++ [v])).
      rewrite app_length -(assoc (++)). iSmash.
  Qed.
  Lemma chunk_foldri_spec_atomic Ψ l sz fn acc :
    (0 ≤ sz)%Z →
    {{{
      Ψ (Z.to_nat sz) acc None [] ∗
      □ (
        ∀ i acc vs,
        ⌜(S i + length vs)%nat = Z.to_nat sz⌝ -∗
        Ψ (S i) acc None vs -∗
        chunk_au_load l i (λ v,
          Ψ (S i) acc (Some v) vs
        )
      ) ∗
      □ (
        ∀ i v acc vs,
        ⌜(S i + length vs)%nat = Z.to_nat sz⌝ -∗
        Ψ (S i) acc (Some v) vs -∗
        WP fn #i v acc {{ acc,
          Ψ i acc None (v :: vs)
        }}
      )
    }}}
      chunk_foldri #l #sz fn acc
    {{{ acc vs,
      RET acc;
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ 0 acc None vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau & #Hfn) HΦ".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp_rec.
    wp_smart_apply (chunk_foldri_aux_spec sz sz [] Ψ with "[$HΨ $Hau $Hfn] [HΦ]"); first done. clear acc. iIntros "!> %acc %vs".
    rewrite !right_id. iSmash.
  Qed.
  Lemma chunk_foldri_spec Ψ l dq vs (sz : Z) fn acc :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn #i v acc {{ acc,
          Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      chunk_foldri #l #sz fn acc
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros (->) "%Φ (Hmodel & HΨ & #Hfn) HΦ".
    pose (Ψ' i acc o vs_done := (
      ⌜vs_done = drop i vs⌝ ∗
      chunk_model l dq vs ∗
      Ψ i acc vs_done ∗
      ⌜from_option (λ v, v = vs !!! (i - 1)) True o⌝%I
    )%I).
    wp_apply (chunk_foldri_spec_atomic Ψ' with "[$Hmodel $HΨ]"); [lia | | iSmash].
    rewrite Nat2Z.id.
    repeat iSplitR.
    - rewrite drop_all. iSmash.
    - clear acc. iIntros "!> %i %acc %vs_done %Hi (-> & Hmodel & HΨ & _)".
      feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
      iDestruct (chunk_model_lookup_acc with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; first iSmash. iIntros "H↦ !>". iSteps;
        iPureIntro; rewrite drop_length; f_equal; lia.
    - clear acc. iIntros "!> %i %v %acc %vs_done %Hi (-> & Hmodel & HΨ & %Hv)". rewrite Hv.
      feed pose proof (list_lookup_lookup_total_lt vs i) as Hlookup; first lia.
      wp_apply (wp_wand with "(Hfn [] HΨ)").
      { iPureIntro. rewrite Hlookup. repeat f_equal. lia. }
      clear acc. iIntros "%acc HΨ". iFrame.
      iPureIntro. rewrite -drop_S ?Hlookup; repeat f_equal; lia.
  Qed.
  Lemma chunk_foldri_spec' Ψ l dq vs (sz : Z) fn acc :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn #i v acc {{ acc,
          Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      chunk_foldri #l #sz fn acc
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros (->) "%Φ (Hmodel & HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i acc vs_done := (
      Ψ i acc vs_done ∗
      [∗ list] j ↦ v ∈ take i vs, Ξ j v
    )%I).
    wp_apply (chunk_foldri_spec Ψ' with "[$Hmodel HΨ Hfn]"); [done | | iSmash].
    iFrame. rewrite firstn_all2; last lia. iFrame.
    clear acc. iIntros "!> %i %v %acc %Hlookup (HΨ & HΞ)".
    pose proof Hlookup as Hi%lookup_lt_Some.
    erewrite take_S_r; last done.
    iDestruct "HΞ" as "(HΞ & Hfn & _)".
    rewrite Nat.add_0_r take_length Nat.min_l; last lia.
    wp_apply (wp_wand with "(Hfn HΨ)"). clear acc. iIntros "%acc HΨ".
    iSmash.
  Qed.

  Lemma chunk_foldr_spec_atomic Ψ l sz fn acc :
    (0 ≤ sz)%Z →
    {{{
      Ψ (Z.to_nat sz) acc None [] ∗
      □ (
        ∀ i acc vs,
        ⌜(S i + length vs)%nat = Z.to_nat sz⌝ -∗
        Ψ (S i) acc None vs -∗
        chunk_au_load l i (λ v,
          Ψ (S i) acc (Some v) vs
        )
      ) ∗
      □ (
        ∀ i v acc vs,
        ⌜(S i + length vs)%nat = Z.to_nat sz⌝ -∗
        Ψ (S i) acc (Some v) vs -∗
        WP fn v acc {{ acc,
          Ψ i acc None (v :: vs)
        }}
      )
    }}}
      chunk_foldr #l #sz fn acc
    {{{ acc vs,
      RET acc;
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ 0 acc None vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldri_spec_atomic Ψ with "[$HΨ $Hau] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_foldr_spec Ψ l dq vs (sz : Z) fn acc :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn v acc {{ acc,
          Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      chunk_foldr #l #sz fn acc
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldri_spec Ψ with "[$Hmodel $HΨ] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_foldr_spec' Ψ l dq vs (sz : Z) fn acc :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn v acc {{ acc,
          Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      chunk_foldr #l #sz fn acc
    {{{ acc,
      RET acc;
      chunk_model l dq vs ∗
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_foldri_spec' Ψ with "[$Hmodel $HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.

  Lemma chunk_iteri_spec_atomic Ψ l sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] None ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs None -∗
        chunk_au_load l i (λ v,
          Ψ i vs (Some v)
        )
      ) ∗
      □ (
        ∀ i vs v,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs (Some v) -∗
        WP fn #i v {{ _,
          Ψ (S i) (vs ++ [v]) None
        }}
      )
    }}}
      chunk_iteri #l #sz fn
    {{{ vs,
      RET #();
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) vs None
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau & #Hfn) HΦ".
    wp_rec.
    pose Ψ' i vs o acc := (
      ⌜acc = #()⌝ ∗
      Ψ i vs o
    )%I.
    wp_smart_apply (chunk_foldli_spec_atomic Ψ' with "[$HΨ]"); [done | | iSmash].
    repeat iSplit; try iSmash. iIntros "!> %i %vs %acc (%Hi& %Hi2) (-> & HΨ)".
    iApply (atomic_update_wand with "(Hau [//] HΨ)").
    iSmash.
  Qed.
  Lemma chunk_iteri_spec Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn #i v {{ _,
          Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_rec.
    pose Ψ' i vs acc := (
      ⌜acc = #()⌝ ∗
      Ψ i vs
    )%I.
    wp_smart_apply (chunk_foldli_spec Ψ' with "[$Hmodel $HΨ]"); [done | iSmash..].
  Qed.
  Lemma chunk_iteri_spec' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ _,
          Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    pose Ψ' i vs acc := (
      ⌜acc = #()⌝ ∗
      Ψ i vs
    )%I.
    wp_smart_apply (chunk_foldli_spec' Ψ' with "[$Hmodel $HΨ Hfn]"); [done | iSteps..].
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.
  Lemma chunk_iteri_spec_disentangled Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ _,
          Ψ i v
        }}
      )
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (chunk_iteri_spec Ψ' with "[$Hmodel]"); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc take_length Nat.min_l; first iSmash.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma chunk_iteri_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ _,
          Ψ i v
        }}
      )
    }}}
      chunk_iteri #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (chunk_iteri_spec' Ψ' with "[$Hmodel Hfn]"); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc take_length Nat.min_l; first iSmash.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma chunk_iter_spec_atomic Ψ l sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] None ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs None -∗
        chunk_au_load l i (λ v,
          Ψ i vs (Some v)
        )
      ) ∗
      □ (
        ∀ i vs v,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs (Some v) -∗
        WP fn v {{ _,
          Ψ (S i) (vs ++ [v]) None
        }}
      )
    }}}
      chunk_iter #l #sz fn
    {{{ vs,
      RET #();
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) vs None
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec_atomic Ψ with "[$HΨ $Hau] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_iter_spec Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn v {{ _,
          Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      chunk_iter #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec Ψ with "[$Hmodel $HΨ] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_iter_spec' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ _,
          Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      chunk_iter #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec' Ψ with "[$Hmodel $HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.
  Lemma chunk_iter_spec_disentangled Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ _,
          Ψ i v
        }}
      )
    }}}
      chunk_iter #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec_disentangled Ψ with "[$Hmodel] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_iter_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ _,
          Ψ i v
        }}
      )
    }}}
      chunk_iter #l #sz fn
    {{{
      RET #();
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.

  Lemma chunk_applyi_spec_atomic Ψ l sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] None [] ∗
      □ (
        ∀ i vs ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs None ws -∗
        chunk_au_load l i (λ v,
          Ψ i vs (Some $ inl v) ws
        )
      ) ∗
      □ (
        ∀ i vs v ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs (Some $ inl v) ws -∗
        WP fn #i v {{ w,
          Ψ i vs (Some $ inr (v, w)) ws
        }}
      ) ∗
      □ (
        ∀ i vs v ws w,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs (Some $ inr (v, w)) ws -∗
        chunk_au_store l i w (
          Ψ (S i) (vs ++ [v]) None (ws ++ [w])
        )
      )
    }}}
      chunk_applyi #l #sz fn
    {{{ vs ws,
      RET #();
      ⌜length vs = Z.to_nat sz ∧ length vs = length ws⌝ ∗
      Ψ (Z.to_nat sz) vs None ws
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau1 & #Hfn & #Hau2) HΦ".
    wp_rec.
    pose (Ψ' i vs o := (
      ∃ ws,
      ⌜length vs = length ws⌝ ∗
      Ψ i vs (inl <$> o) ws
    )%I).
    wp_smart_apply (chunk_iteri_spec_atomic Ψ' with "[HΨ]"); [done | | iSmash].
    iSplitL "HΨ". { iExists []. iSmash. }
    iSplit; iIntros "!> %i %vs".
    - iIntros "(%Hi1 & %Hi2) (%ws & %Hws & HΨ)".
      iApply (atomic_update_wand with "(Hau1 [//] HΨ)").
      iSmash.
    - iIntros "%v (%Hi1 & %Hi2) (%ws & %Hws & HΨ)".
      wp_smart_apply (wp_wand with "(Hfn [//] HΨ)"). iIntros "%w HΨ".
      wp_pures.
      iMod ("Hau2" with "[//] HΨ") as "(%v' & H↦ & _ & Hau2')".
      wp_store.
      iExists (ws ++ [w]).
      iMod ("Hau2'" with "H↦") as "$".
      rewrite !app_length. iSmash.
  Qed.
  Lemma chunk_applyi_spec Ψ l vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      Ψ 0 [] [] ∗
      □ (
        ∀ i v ws,
        ⌜i = length ws ∧ vs !! i = Some v⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_applyi #l #sz fn
    {{{ ws,
      RET #();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws
    }}}.
  Proof.
    iIntros (->) "%Φ (Hmodel & HΨ & #Hfn) HΦ".
    pose (Ψ' i vs_done o ws := (
      ⌜vs_done = take i vs⌝ ∗
      chunk_model l (DfracOwn 1) (ws ++ drop i vs) ∗
      match o with
      | None =>
          Ψ i vs_done ws
      | Some (inl v) =>
          ⌜v = vs !!! i⌝ ∗
          Ψ i vs_done ws
      | Some (inr (v, w)) =>
          ⌜v = vs !!! i⌝ ∗
          Ψ (S i) (vs_done ++ [v]) (ws ++ [w])
      end
    )%I).
    wp_apply (chunk_applyi_spec_atomic Ψ' with "[$Hmodel $HΨ]"); first lia; last first.
    { iIntros "%vs_done %ws ((%Hvs_done_1 & %Hws) & (-> & Hmodel & HΨ))".
      rewrite Nat2Z.id firstn_all2; last lia. rewrite skipn_all2; last lia. rewrite right_id.
      iApply ("HΦ" $! ws). iSmash.
    }
    iSplit; first iSmash. repeat iSplit.
    - iIntros "!> %i %vs_done %ws (%Hvs_done & %Hi & %Hws) (-> & Hmodel & HΨ)".
      assert ((ws ++ drop i vs) !! i = Some (vs !!! i)).
      { rewrite lookup_app_r; last lia.
        rewrite lookup_drop list_lookup_lookup_total_lt; last lia.
        repeat f_equal. lia.
      }
      iDestruct (chunk_model_lookup_acc with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; iSmash.
    - iIntros "!> %i %vs_done %v %ws (%Hvs_done & %Hi & %Hws) (-> & Hmodel & -> & HΨ)".
      feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
      wp_apply (wp_wand with "(Hfn [] HΨ)"); iSmash.
    - iIntros "!> %i %vs_done %v %ws %w (%Hvs_done & %Hi & %Hws) (-> & Hmodel & -> & HΨ)".
      feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
      assert ((ws ++ drop i vs) !! i = Some (vs !!! i)).
      { rewrite lookup_app_r; last lia.
        rewrite lookup_drop list_lookup_lookup_total_lt; last lia.
        repeat f_equal. lia.
      }
      iDestruct (chunk_model_update with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; first iSmash. iIntros "H↦ !>". iFrame.
      iSplit; first rewrite -take_S_r //.
      iDestruct ("Hmodel" with "H↦") as "Hmodel".
      rewrite insert_app_r_alt; last lia.
      erewrite drop_S; last done.
      rewrite Hi Hws Nat.sub_diag -assoc //.
  Qed.
  Lemma chunk_applyi_spec' Ψ l vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      Ψ 0 [] [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_applyi #l #sz fn
    {{{ ws,
      RET #();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_done ws := (
      Ψ i vs_done ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (chunk_applyi_spec Ψ' with "[$Hmodel HΨ Hfn]"); [done | | iSmash].
    iFrame. iIntros "!> %i %v %ws (%Hi & %Hlookup) (HΨ & HΞ)".
    erewrite drop_S; last done.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r.
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iIntros "%w HΨ". iFrame.
    setoid_rewrite Nat.add_succ_r. iSmash.
  Qed.
  Lemma chunk_applyi_spec_disentangled Ψ l vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ w,
          Ψ i w
        }}
      )
    }}}
      chunk_applyi #l #sz fn
    {{{ ws,
      RET #();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs_done ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp_apply (chunk_applyi_spec Ψ' with "[$Hmodel]"); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSmash.
  Qed.
  Lemma chunk_applyi_spec_disentangled' Ψ l vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          Ψ i w
        }}
      )
    }}}
      chunk_applyi #l #sz fn
    {{{ ws,
      RET #();
      chunk_model l (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs_done ws := (
      [∗ list] j ↦ w ∈ ws, Ψ j w
    )%I).
    wp_apply (chunk_applyi_spec' Ψ' with "[Hmodel Hfn]"); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSmash.
  Qed.

  Lemma chunk_apply_spec_atomic Ψ l sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] None [] ∗
      □ (
        ∀ i vs ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs None ws -∗
        chunk_au_load l i (λ v,
          Ψ i vs (Some $ inl v) ws
        )
      ) ∗
      □ (
        ∀ i vs v ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs (Some $ inl v) ws -∗
        WP fn v {{ w,
          Ψ i vs (Some $ inr (v, w)) ws
        }}
      ) ∗
      □ (
        ∀ i vs v ws w,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs (Some $ inr (v, w)) ws -∗
        chunk_au_store l i w (
          Ψ (S i) (vs ++ [v]) None (ws ++ [w])
        )
      )
    }}}
      chunk_apply #l #sz fn
    {{{ vs ws,
      RET #();
      ⌜length vs = Z.to_nat sz ∧ length vs = length ws⌝ ∗
      Ψ (Z.to_nat sz) vs None ws
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau1 & #Hfn & #Hau2) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_spec_atomic Ψ with "[$HΨ $Hau1 $Hau2] HΦ"); first done. iIntros "!> %i %vs %v %ws (%Hi1 & %Hi2 & %Hws) HΨ".
    wp_smart_apply (wp_wand with "(Hfn [//] HΨ)").
    iSmash.
  Qed.
  Lemma chunk_apply_spec Ψ l vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      Ψ 0 [] [] ∗
      □ (
        ∀ i v ws,
        ⌜i = length ws ∧ vs !! i = Some v⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_apply #l #sz fn
    {{{ ws,
      RET #();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_spec Ψ with "[$Hmodel $HΨ] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_apply_spec' Ψ l vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      Ψ 0 [] [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_apply #l #sz fn
    {{{ ws,
      RET #();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_spec' Ψ with "[$Hmodel $HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.
  Lemma chunk_apply_spec_disentangled Ψ l vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ w,
          Ψ i w
        }}
      )
    }}}
      chunk_apply #l #sz fn
    {{{ ws,
      RET #();
      ⌜length vs = length ws⌝ ∗
      chunk_model l (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_spec_disentangled Ψ with "[$Hmodel] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_apply_spec_disentangled' Ψ l vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          Ψ i w
        }}
      )
    }}}
      chunk_apply #l #sz fn
    {{{ ws,
      RET #();
      chunk_model l (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ w ∈ ws,
        Ψ i w
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_applyi_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.

  Lemma chunk_initi_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      chunk_initi #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_make_spec with "[//]"); first done. iIntros "%l (Hmodel & Hmeta)".
    pose Ψ' i vs' vs := (
      Ψ i vs
    )%I.
    wp_smart_apply (chunk_applyi_spec Ψ' with "[$Hmodel $HΨ]"); last 1 first.
    { iIntros "%vs (%Hvs & Hmodel & HΨ)". rewrite replicate_length in Hvs.
      wp_pures.
      iApply ("HΦ" $! _ vs).
      iSmash.
    } {
      rewrite replicate_length. lia.
    }
    iIntros "!> %i %v %vs (%Hi & %Hv) HΨ". apply lookup_replicate in Hv.
    iSmash.
  Qed.
  Lemma chunk_initi_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      chunk_initi #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (Z.to_nat sz - i), Ξ j
    )%I).
    wp_apply (chunk_initi_spec Ψ' with "[$HΨ Hfn]"); [done | | iSmash].
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (Z.to_nat sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma chunk_initi_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn #i {{ v,
          Ψ i v
        }}
      )
    }}}
      chunk_initi #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      ) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (chunk_initi_spec Ψ'); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSmash.
  Qed.
  Lemma chunk_initi_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #i {{ v,
          Ψ i v
        }}
      )
    }}}
      chunk_initi #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      ) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (chunk_initi_spec' Ψ' with "[Hfn]"); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSmash.
  Qed.

  Lemma chunk_init_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #() {{ v,
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_initi_spec Ψ with "[$HΨ] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_init_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #() {{ v,
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_initi_spec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.
  Lemma chunk_init_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn #() {{ v,
          Ψ i v
        }}
      )
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      ) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply (chunk_initi_spec_disentangled Ψ with "[] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_init_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #() {{ v,
          Ψ i v
        }}
      )
    }}}
      chunk_init #sz fn
    {{{ l vs,
      RET #l;
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      ) ∗
      if decide (0 < sz)%Z then meta_token l ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".
    wp_rec.
    wp_smart_apply (chunk_initi_spec_disentangled' Ψ with "[Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.

  Lemma chunk_mapi_spec_atomic Ψ l sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] None [] ∗
      □ (
        ∀ i vs ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs None ws -∗
        chunk_au_load l i (λ v,
          Ψ i vs (Some v) ws
        )
      ) ∗
      □ (
        ∀ i vs v ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs (Some v) ws -∗
        WP fn #i v {{ w,
          Ψ (S i) (vs ++ [v]) None (ws ++ [w])
        }}
      )
    }}}
      chunk_mapi #l #sz fn
    {{{ l' vs ws,
      RET #l';
      ⌜length vs = Z.to_nat sz ∧ length vs = length ws⌝ ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs None ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau & #Hfn) HΦ".
    wp_rec.
    pose Ψ' i ws := (
      ∃ vs,
      ⌜length vs = length ws⌝ ∗
      Ψ i vs None ws
    )%I.
    wp_smart_apply (chunk_initi_spec Ψ' with "[HΨ]"); first done; last first.
    { iIntros "%l' %ws (%Hws & Hmodel & (%vs & %Hvs & HΨ) & Hmeta)".
      iApply ("HΦ" with "[$Hmodel $HΨ $Hmeta]").
      iSmash.
    }
    iSplit. { iExists []. iSmash. }
    iIntros "!> %i %ws (%Hi1 & %Hi2) (%vs & %Hvs & HΨ)".
    wp_pures. wp_bind (!_)%E.
    iMod ("Hau" with "[] HΨ") as "(%dq & %v & H↦ & _ & HΨ)"; first iSmash.
    wp_load.
    iMod ("HΨ" with "H↦") as "HΨ". iModIntro.
    wp_apply (wp_wand with "(Hfn [] HΨ)"); first iSmash. iIntros "%w HΨ".
    iExists (vs ++ [v]). iFrame. rewrite !app_length. iSmash.
  Qed.
  Lemma chunk_mapi_spec Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] [] ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v ∧ i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & #Hfn) HΦ".
    pose (Ψ' i vs_done o ws := (
      ⌜vs_done = take i vs⌝ ∗
      chunk_model l dq vs ∗
      Ψ i vs_done ws ∗
      ⌜from_option (λ v, v = vs !!! i) True o⌝%I
    )%I).
    wp_apply (chunk_mapi_spec_atomic Ψ' with "[$Hmodel $HΨ]"); last first.
    { iIntros "%l' %vs_done %ws ((%Hvs_done & %Hws) & Hmodel' & (-> & Hmodel & HΨ & _) & Hmeta)".
      rewrite /Ψ' firstn_all2; last lia. iSmash.
    }
    repeat iSplitR.
    - iSmash.
    - iIntros "!> %i %vs_done %ws (%Hi & _ & %Hws) (%Hvs_done & Hmodel & HΨ & _)".
      feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
      iDestruct (chunk_model_lookup_acc with "Hmodel") as "(H↦ & Hmodel)"; first done.
      iAuIntro. iAaccIntro with "H↦"; iSmash.
    - iIntros "!> %i %vs_done %v %ws (%Hi1 & %Hi2 & %Hws) (-> & Hmodel & HΨ & %Hv)". rewrite Hv.
      feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
      wp_apply (wp_wand with "(Hfn [] HΨ)"); first iSmash. iIntros "%w HΨ". iFrame.
      erewrite take_S_r; done.
    - lia.
  Qed.
  Lemma chunk_mapi_spec' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_done ws := (
      Ψ i vs_done ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (chunk_mapi_spec Ψ' with "[$Hmodel HΨ Hfn]"); [done | | iSmash].
    iFrame. iIntros "!> %i %v %ws (%Hlookup & %Hi) (HΨ & HΞ)".
    erewrite drop_S; last done.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r.
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iIntros "%w HΨ". iFrame.
    setoid_rewrite Nat.add_succ_r. iSmash.
  Qed.
  Lemma chunk_mapi_spec_disentangled Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ w,
          Ψ i v w
        }}
      )
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      ) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    pose Ψ' i vs_done ws := (
      [∗ list] j ↦ v; w ∈ vs_done; ws, Ψ j v w
    )%I.
    wp_apply (chunk_mapi_spec Ψ' with "[$Hmodel]"); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL2_snoc take_length Nat.min_l; first iSmash.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma chunk_mapi_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          Ψ i v w
        }}
      )
    }}}
      chunk_mapi #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      ) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    pose Ψ' i vs_done ws := (
      [∗ list] j ↦ v; w ∈ vs_done; ws, Ψ j v w
    )%I.
    wp_apply (chunk_mapi_spec' Ψ' with "[Hmodel Hfn]"); first done; last first.
    { iIntros "%l' %ws (Hmodel & Hmodel' & HΨ & Hmeta)".
      iSmash.
    }
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL2_snoc take_length Nat.min_l; first iSmash.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma chunk_map_spec_atomic Ψ l sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] None [] ∗
      □ (
        ∀ i vs ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs None ws -∗
        chunk_au_load l i (λ v,
          Ψ i vs (Some v) ws
        )
      ) ∗
      □ (
        ∀ i vs v ws,
        ⌜i < Z.to_nat sz ∧ i = length vs ∧ length vs = length ws⌝ -∗
        Ψ i vs (Some v) ws -∗
        WP fn v {{ w,
          Ψ (S i) (vs ++ [v]) None (ws ++ [w])
        }}
      )
    }}}
      chunk_map #l #sz fn
    {{{ l' vs ws,
      RET #l';
      ⌜length vs = Z.to_nat sz ∧ length vs = length ws⌝ ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs None ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec_atomic Ψ with "[$HΨ $Hau] HΦ"); first done. iIntros "!> %i %vs %v %ws (%Hi1 & %Hi2 & %Hws) HΨ".
    wp_smart_apply ("Hfn" with "[//] HΨ").
  Qed.
  Lemma chunk_map_spec Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] [] ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v ∧ i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec Ψ with "[$Hmodel $HΨ] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_map_spec' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      Ψ 0 [] [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      Ψ (Z.to_nat sz) vs ws ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec' Ψ with "[$Hmodel $HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.
  Lemma chunk_map_spec_disentangled Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ w,
          Ψ i v w
        }}
      )
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      ) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec_disentangled Ψ with "[$Hmodel] HΦ"); first done.
    iSmash.
  Qed.
  Lemma chunk_map_spec_disentangled' Ψ l dq vs (sz : Z) fn :
    sz = length vs →
    {{{
      chunk_model l dq vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          Ψ i v w
        }}
      )
    }}}
      chunk_map #l #sz fn
    {{{ l' ws,
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      ) ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (chunk_mapi_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSmash.
  Qed.

  Lemma chunk_copy_spec_atomic Ψ l1 l2 sz :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] None ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs None -∗
        chunk_au_load l1 i (λ v,
          Ψ i vs (Some v)
        )
      ) ∗
      □ (
        ∀ i vs v,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs (Some v) -∗
        chunk_au_store l2 i v (
          Ψ (S i) (vs ++ [v]) None
        )
      )
    }}}
      chunk_copy #l1 #sz #l2
    {{{ vs,
      RET #();
      ⌜length vs = Z.to_nat sz⌝ ∗
      Ψ (Z.to_nat sz) vs None
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau1 & #Hau2) HΦ".
    wp_rec.
    wp_smart_apply (chunk_iteri_spec_atomic Ψ with "[$HΨ]"); [done | | iSmash].
    iSplit; first iSmash. iIntros "!> %i %vs %v (%Hi1 & %Hi2) HΨ".
    wp_pures.
    iMod ("Hau2" with "[] HΨ") as "(%v' & H↦ & _ & HΨ)"; first iSmash.
    wp_store.
    iApply ("HΨ" with "H↦").
  Qed.
  Lemma chunk_copy_spec l1 dq1 vs1 (sz : Z) l2 vs2 :
    sz = length vs1 →
    sz = length vs2 →
    {{{
      chunk_model l1 dq1 vs1 ∗
      chunk_model l2 (DfracOwn 1) vs2
    }}}
      chunk_copy #l1 #sz #l2
    {{{
      RET #();
      chunk_model l1 dq1 vs1 ∗
      chunk_model l2 (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros "%Hvs1 %Hvs2 %Φ (Hmodel1 & Hmodel2) HΦ".
    pose (Ψ i vs1_done o := (
      ⌜vs1_done = take i vs1⌝ ∗
      chunk_model l1 dq1 vs1 ∗
      chunk_model l2 (DfracOwn 1) (vs1_done ++ drop i vs2) ∗
      ⌜from_option (λ v1, vs1 !! i = Some v1) True o⌝
    )%I).
    wp_apply (chunk_copy_spec_atomic Ψ with "[$Hmodel1 $Hmodel2]"); first lia; last first.
    { iIntros "%vs1_done (_ & (-> & Hmodel1 & Hmodel2 & _))".
      iApply ("HΦ" with "[$Hmodel1 Hmodel2]").
      rewrite firstn_all2; last lia. rewrite skipn_all2; last lia. rewrite right_id //.
    }
    repeat iSplit; first iSmash.
    - iIntros "!> %i %vs1_done (%Hi & _) (-> & Hmodel1 & Hmodel2 & _)".
      feed pose proof (list_lookup_lookup_total_lt vs1 i); first lia.
      iDestruct (chunk_model_lookup_acc with "Hmodel1") as "(H↦1 & Hmodel1)"; first done.
      iAuIntro. iAaccIntro with "H↦1"; iSmash.
    - iIntros "!> %i %vs1_done %v1 (%Hi & _) (-> & Hmodel1 & Hmodel2 & %Hlookup)".
      feed pose proof (list_lookup_lookup_total_lt vs2 i); first lia.
      iDestruct (chunk_model_update with "Hmodel2") as "(H↦2 & Hmodel2)".
      { rewrite lookup_app_r take_length Nat.min_l //; try lia.
        rewrite Nat.sub_diag lookup_drop right_id list_lookup_lookup_total_lt //. lia.
      }
      iAuIntro. iAaccIntro with "H↦2"; first iSmash. iIntros "H↦2".
      iDestruct ("Hmodel2" with "H↦2") as "Hmodel2".
      iFrame. iSplitR. { erewrite take_S_r; done. }
      rewrite insert_app_r_alt take_length Nat.min_l //; try lia.
      rewrite Nat.sub_diag. erewrite drop_S; last done. rewrite -(assoc (++)).
      iSmash.
  Qed.

  Lemma chunk_resize_spec_atomic Ψ l sz sz' n v' :
    (0 ≤ n ≤ sz)%Z →
    (0 ≤ n ≤ sz')%Z →
    {{{
      Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat n ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        chunk_au_load l i (λ v,
          Ψ (S i) (vs ++ [v])
        )
      )
    }}}
      chunk_resize #l #sz #sz' #n v'
    {{{ l' vs,
      RET #l';
      ⌜length vs = Z.to_nat n⌝ ∗
      chunk_model l' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - Z.to_nat n) v') ∗
      Ψ (Z.to_nat n) vs ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros ((Hsz1 & Hsz2) (Hsz'1 & Hsz'2)) "%Φ (HΨ & #Hau) HΦ".
    wp_rec.
    wp_smart_apply (chunk_make_spec with "[//]"); first lia. iIntros "%l' (Hmodel' & Hmeta)".
    pose Ψ' i vs o := (
      chunk_model l' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - i) v') ∗
      from_option (λ v, Ψ (S i) (vs ++ [v])) (Ψ i vs) o
    )%I.
    wp_smart_apply (chunk_copy_spec_atomic Ψ' with "[Hmodel' $HΨ]"); [done | | iSmash].
    repeat iSplit.
    - rewrite Nat.sub_0_r. iSmash.
    - iIntros "!> %i %vs (%Hi1 & %Hi2) (Hmodel' & HΨ)".
      iApply (atomic_update_wand with "(Hau [//] HΨ)").
      iSmash.
    - iIntros "!> %i %vs %v (%Hi1 & %Hi2) (Hmodel' & HΨ)".
      iDestruct (chunk_model_update i with "Hmodel'") as "(H↦ & Hmodel')".
      { rewrite Hi2 lookup_app_r //. rewrite Nat.sub_diag lookup_replicate.
        naive_solver lia.
      }
      iAuIntro. iAaccIntro with "H↦"; first iSmash. iIntros "H↦ !>". iFrame.
      iDestruct ("Hmodel'" with "H↦") as "Hmodel'".
      rewrite insert_app_r_alt; last lia. rewrite insert_replicate_lt; last lia.
      rewrite Hi2 Nat.sub_diag /= Nat.sub_1_r -Nat.sub_succ_r -(assoc (++)).
      iSmash.
  Qed.
  Lemma chunk_resize_spec l dq vs (sz : Z) sz' n v' :
    sz = length vs →
    (n ≤ sz)%Z →
    (0 ≤ n ≤ sz')%Z →
    {{{
      chunk_model l dq vs
    }}}
      chunk_resize #l #sz #sz' #n v'
    {{{ l',
      RET #l';
      chunk_model l dq vs ∗
      chunk_model l' (DfracOwn 1) (take (Z.to_nat n) vs ++ replicate (Z.to_nat sz' - Z.to_nat n) v') ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros (Hsz1 Hsz2 (Hsz'1 & Hsz'2)) "%Φ Hmodel HΦ".
    pose Ψ i vs_done := (
      ⌜vs_done = take i vs⌝ ∗
      chunk_model l dq vs
    )%I.
    wp_apply (chunk_resize_spec_atomic Ψ with "[$Hmodel]"); [done.. | | iSmash].
    iStep. iIntros "!> %i %vs_done (%Hi1 & %Hi2) (-> & Hmodel)".
    feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
    iDestruct (chunk_model_lookup_acc i with "Hmodel") as "(H↦ & Hmodel)"; first done.
    iAuIntro. iAaccIntro with "H↦"; first iSmash.
    rewrite -take_S_r //. iSmash.
  Qed.

  Lemma chunk_grow_spec_atomic Ψ l sz sz' v' :
    (0 ≤ sz ≤ sz')%Z →
    {{{
      Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        chunk_au_load l i (λ v,
          Ψ (S i) (vs ++ [v])
        )
      )
    }}}
      chunk_grow #l #sz #sz' v'
    {{{ l' vs,
      RET #l';
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - Z.to_nat sz) v') ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros ((Hsz & Hsz')) "%Φ (HΨ & #Hau) HΦ".
    wp_rec.
    wp_smart_apply (chunk_resize_spec_atomic Ψ with "[$HΨ $Hau]"); [done.. | iSmash].
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
      chunk_model l' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - Z.to_nat sz) v) ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Hsz' %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (chunk_resize_spec with "Hmodel"); [lia.. |].
    iSteps. rewrite firstn_all2; last lia. iSmash.
  Qed.

  Lemma chunk_shrink_spec_atomic Ψ l sz sz' :
    (0 ≤ sz' ≤ sz)%Z →
    {{{
      Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz' ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        chunk_au_load l i (λ v,
          Ψ (S i) (vs ++ [v])
        )
      )
    }}}
      chunk_shrink #l #sz #sz'
    {{{ l' vs,
      RET #l';
      ⌜length vs = Z.to_nat sz'⌝ ∗
      chunk_model l' (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz') vs ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros ((Hsz & Hsz')) "%Φ (HΨ & #Hau) HΦ".
    wp_rec.
    wp_smart_apply (chunk_resize_spec_atomic Ψ with "[$HΨ $Hau]"); [done.. |].
    iSteps. rewrite Nat.sub_diag right_id. iSmash.
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
      chunk_model l' (DfracOwn 1) (take (Z.to_nat sz') vs) ∗
      if decide (0 < sz')%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Hsz' %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (chunk_resize_spec with "Hmodel"); [lia.. |].
    iSteps. rewrite Nat.sub_diag right_id. iSmash.
  Qed.

  Lemma chunk_clone_spec_atomic Ψ l sz :
    (0 ≤ sz)%Z →
    {{{
      Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        chunk_au_load l i (λ v,
          Ψ (S i) (vs ++ [v])
        )
      )
    }}}
      chunk_clone #l #sz
    {{{ l' vs,
      RET #l';
      ⌜length vs = Z.to_nat sz⌝ ∗
      chunk_model l' (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hau) HΦ".
    wp_rec.
    wp_smart_apply (chunk_shrink_spec_atomic Ψ with "[$HΨ $Hau]"); [done | iSmash].
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
      chunk_model l' (DfracOwn 1) vs ∗
      if decide (0 < sz)%Z then meta_token l' ⊤ else True
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (chunk_shrink_spec with "Hmodel"); [lia.. |]. iIntros "%l' (Hmodel & Hmodel' & Hmeta)".
    iApply "HΦ".
    rewrite Hsz Nat2Z.id firstn_all. iSmash.
  Qed.
End heapGS.

#[global] Opaque chunk_make.
#[global] Opaque chunk_foldli.
#[global] Opaque chunk_foldl.
#[global] Opaque chunk_foldri.
#[global] Opaque chunk_foldr.
#[global] Opaque chunk_iteri.
#[global] Opaque chunk_iter.
#[global] Opaque chunk_applyi.
#[global] Opaque chunk_apply.
#[global] Opaque chunk_initi.
#[global] Opaque chunk_init.
#[global] Opaque chunk_mapi.
#[global] Opaque chunk_map.
#[global] Opaque chunk_copy.
#[global] Opaque chunk_resize.
#[global] Opaque chunk_grow.
#[global] Opaque chunk_shrink.
#[global] Opaque chunk_clone.

#[global] Opaque chunk_model.
#[global] Opaque chunk_span.
