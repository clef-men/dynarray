From ml Require Import
  prelude.
From ml.bi Require Import
  big_op.
From ml.language Require Import
  notations
  proofmode.
From ml.std Require Export
  base.
From ml.std Require Import
  assume
  chunk.

Section heapGS.
  Context `{!heapGS Σ}.

  Implicit Types i j n : nat.
  Implicit Types l : loc.
  Implicit Types v t fn : val.
  Implicit Types vs : list val.

  Notation "t '.[size]'" :=
    t.[0]%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.[data]'" :=
    t.[1]%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.[size]'" :=
    t.[0]%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.[data]'" :=
    t.[1]%E
  ( at level 5
  ) : expr_scope.

  Definition array_create : val :=
    λ: <>,
      chunk_make #1 #0.

  Definition array_make : val :=
    λ: "sz" "v",
      assume (#0 ≤ "sz") ;;
      let: "t" := chunk_make (#1 + "sz") "v" in
      "t".[size] <- "sz" ;;
      "t".

  Definition array_initi : val :=
    λ: "sz" "fn",
      assume (#0 ≤ "sz") ;;
      let: "t" := chunk_make (#1 + "sz") "sz" in
      chunk_applyi "t".[data] "sz" (λ: "i" <>, "fn" "i") ;;
      "t".

  Definition array_size : val :=
    λ: "t",
      !"t".[size].
  #[local] Definition array_data : val :=
    λ: "t",
      "t".[data].

  Definition array_unsafe_get : val :=
    λ: "t" "i",
      !(array_data "t" +ₗ "i").
  Definition array_get : val :=
    λ: "t" "i",
      assume (#0 ≤ "i") ;;
      assume ("i" < array_size "t") ;;
      array_unsafe_get "t" "i".

  Definition array_unsafe_set : val :=
    λ: "t" "i" "v",
      array_data "t" +ₗ "i" <- "v".
  Definition array_set : val :=
    λ: "t" "i" "v",
      assume (#0 ≤ "i") ;;
      assume ("i" < array_size "t") ;;
      array_unsafe_set "t" "i" "v".

  Definition array_blit : val :=
    λ: "t1" "i1" "t2" "i2" "n",
      let: "sz1" := array_size "t1" in
      let: "sz2" := array_size "t2" in
      assume (#0 ≤ "i1") ;;
      assume ("i1" < "sz1") ;;
      assume (#0 ≤ "i2") ;;
      assume ("i2" < "sz2") ;;
      assume (#0 ≤ "n") ;;
      assume (#0 ≤ "i1" + "n") ;;
      assume ("i1" + "n" < "sz1") ;;
      assume (#0 ≤ "i2" + "n") ;;
      assume ("i2" + "n" < "sz2") ;;
      chunk_copy (array_data "t1" +ₗ "i1") "n" (array_data "t2" +ₗ "i2").

  Section array_slice.
    Definition array_slice t (sz : nat) i dq vs : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l.[size] ↦□ #sz ∗
      chunk_model (l.[data] +ₗ i) dq vs.

    #[global] Instance array_slice_timeless t sz i dq vs :
      Timeless (array_slice t sz i dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_slice_persistent t sz i vs :
      Persistent (array_slice t sz i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_slice_fractional t sz i vs :
      Fractional (λ q, array_slice t sz i (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & #Hsz & Hmodel1 & Hmodel2)". iSmash.
      - iIntros "((%l & -> & #Hsz & Hmodel1) & (%_l & %Heq & _ & Hmodel2))". injection Heq as <-.
        iExists l. iSteps.
        iApply chunk_model_fractional. iSmash.
    Qed.
    #[global] Instance array_slice_as_fractional t sz i q vs :
      AsFractional (array_slice t sz i (DfracOwn q) vs) (λ q, array_slice t sz i (DfracOwn q) vs) q.
    Proof.
      split; done || apply _.
    Qed.

    Lemma array_slice_agree_size t sz1 i1 dq1 vs1 sz2 i2 dq2 vs2 :
      array_slice t sz1 i1 dq1 vs1 -∗
      array_slice t sz2 i2 dq2 vs2 -∗
      ⌜sz1 = sz2⌝.
    Proof.
      iIntros "(%l & -> & #Hsz1 & Hmodel1) (%_l & %Heq & #Hsz2 & Hmodel2)". injection Heq as <-.
      iDestruct (mapsto_agree with "Hsz1 Hsz2") as %[= <-%(inj _)].
      iSmash.
    Qed.

    Lemma array_slice_valid t sz i dq vs :
      0 < length vs →
      array_slice t sz i dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%l & -> & #Hsz & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first done.
    Qed.
    Lemma array_slice_combine t i sz1 dq1 vs1 sz2 dq2 vs2 :
      length vs1 = length vs2 →
      array_slice t sz1 i dq1 vs1 -∗
      array_slice t sz2 i dq2 vs2 -∗
        ⌜sz1 = sz2 ∧ vs1 = vs2⌝ ∗
        array_slice t sz1 i (dq1 ⋅ dq2) vs1.
    Proof.
      iIntros "% (%l & -> & #Hsz1 & Hmodel1) (%_l & %Heq & #Hsz2 & Hmodel2)". injection Heq as <-.
      iDestruct (mapsto_agree with "Hsz1 Hsz2") as %[= <-%(inj _)].
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)"; first done.
      iSmash.
    Qed.
    Lemma array_slice_valid_2 t i sz1 dq1 vs1 sz2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_slice t sz1 i dq1 vs1 -∗
      array_slice t sz2 i dq2 vs2 -∗
      ⌜sz1 = sz2 ∧ ✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% % Hslice1 Hslice2".
      iDestruct (array_slice_combine with "Hslice1 Hslice2") as "((<- & <-) & Hslice)"; first done.
      iDestruct (array_slice_valid with "Hslice") as %?; done.
    Qed.
    Lemma array_slice_agree t i sz1 dq1 vs1 sz2 dq2 vs2 :
      length vs1 = length vs2 →
      array_slice t sz1 i dq1 vs1 -∗
      array_slice t sz2 i dq2 vs2 -∗
      ⌜sz1 = sz2 ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% Hslice1 Hslice2".
      iDestruct (array_slice_combine with "Hslice1 Hslice2") as "(% & _)"; done.
    Qed.
    Lemma array_slice_dfrac_ne t1 sz1 i1 dq1 vs1 t2 sz2 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_slice t1 sz1 i1 dq1 vs1 -∗
      array_slice t2 sz2 i2 dq2 vs2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      rewrite -not_and_r. iIntros "% % % Hslice1 Hslice2" ((-> & ->)).
      iDestruct (array_slice_valid_2 with "Hslice1 Hslice2") as %?; naive_solver.
    Qed.
    Lemma array_slice_ne t1 sz1 i1 vs1 t2 sz2 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_slice t1 sz1 i1 (DfracOwn 1) vs1 -∗
      array_slice t2 sz2 i2 dq2 vs2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      intros.
      iApply array_slice_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_slice_exclusive t i sz1 vs1 sz2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_slice t sz1 i (DfracOwn 1) vs1 -∗
      array_slice t sz2 i (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% % Hslice1 Hslice2".
      iDestruct (array_slice_valid_2 with "Hslice1 Hslice2") as %?; naive_solver.
    Qed.
    Lemma array_slice_persist t sz i dq vs :
      array_slice t sz i dq vs ⊢ |==>
      array_slice t sz i DfracDiscarded vs.
    Proof.
      iIntros "(%l & -> & #Hsz & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iSmash.
    Qed.

    Lemma array_slice_app t sz i dq vs1 vs2 :
      array_slice t sz i dq vs1 ∗ array_slice t sz (i + length vs1) dq vs2 ⊣⊢
      array_slice t sz i dq (vs1 ++ vs2).
    Proof.
      iSplit.
      - iIntros "((%l & -> & #Hsz & Hmodel1) & (%_l & %Heq & _ & Hmodel2))". injection Heq as <-.
        rewrite Nat2Z.inj_add -Loc.add_assoc.
        iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel"; first done.
        iSmash.
      - iIntros "(%l & -> & #Hsz & Hmodel)".
        iDestruct (chunk_model_app with "Hmodel") as "(Hmodel1 & Hmodel2)".
        iSplitL "Hmodel1"; iExists l; first iSmash.
        rewrite Loc.add_assoc -Nat2Z.inj_add. iSmash.
    Qed.
    Lemma array_slice_app_1 t sz i dq sz1 vs1 vs2 :
      sz1 = length vs1 →
      array_slice t sz i dq vs1 -∗
      array_slice t sz (i + sz1) dq vs2 -∗
      array_slice t sz i dq (vs1 ++ vs2).
    Proof.
      intros ->. rewrite -array_slice_app. iSmash.
    Qed.
    Lemma array_slice_app_2 t sz i dq vs vs1 vs2 :
      vs = vs1 ++ vs2 →
      array_slice t sz i dq vs ⊢
        array_slice t sz i dq vs1 ∗
        array_slice t sz (i + length vs1) dq vs2.
    Proof.
      intros ->. rewrite array_slice_app //.
    Qed.
  End array_slice.

  Section array_model.
    Definition array_model t dq vs : iProp Σ :=
      array_slice t (length vs) 0 dq vs.

    Lemma array_slice_model t sz dq vs :
      sz = length vs →
      array_slice t sz 0 dq vs ⊢
      array_model t dq vs.
    Proof.
      iSmash.
    Qed.
    Lemma array_model_slice t dq vs :
      array_model t dq vs ⊢
      array_slice t (length vs) 0 dq vs.
    Proof.
      iSmash.
    Qed.

    #[global] Instance array_model_timeless t dq vs :
      Timeless (array_model t dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_model_persistent t vs :
      Persistent (array_model t DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_model_fractional t vs :
      Fractional (λ q, array_model t (DfracOwn q) vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_model_as_fractional t q vs :
      AsFractional (array_model t (DfracOwn q) vs) (λ q, array_model t (DfracOwn q) vs) q.
    Proof.
      apply _.
    Qed.

    Lemma array_model_valid t dq vs :
      0 < length vs →
      array_model t dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      apply array_slice_valid.
    Qed.
    Lemma array_model_combine t dq1 vs1 dq2 vs2 :
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        array_model t (dq1 ⋅ dq2) vs1.
    Proof.
      iIntros "Hmodel1 Hmodel2".
      iDestruct (array_slice_agree_size with "Hmodel1 Hmodel2") as %?.
      iDestruct (array_slice_combine with "Hmodel1 Hmodel2") as "(% & Hmodel)"; naive_solver.
    Qed.
    Lemma array_model_valid_2 t dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_model_combine with "Hmodel1 Hmodel2") as "(-> & Hmodel)".
      iDestruct (array_model_valid with "Hmodel") as %?; done.
    Qed.
    Lemma array_model_agree t dq1 vs1 dq2 vs2 :
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "Hmodel1 Hmodel2".
      iDestruct (array_model_combine with "Hmodel1 Hmodel2") as "(-> & _)".
      iSmash.
    Qed.
    Lemma array_model_dfrac_ne t1 dq1 vs1 t2 dq2 vs2 :
      0 < length vs1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_model t1 dq1 vs1 -∗
      array_model t2 dq2 vs2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2" (->).
      iDestruct (array_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array_model_ne t1 vs1 t2 dq2 vs2 :
      0 < length vs1 →
      array_model t1 (DfracOwn 1) vs1 -∗
      array_model t2 dq2 vs2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      intros. iApply array_model_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_model_exclusive t vs1 vs2 :
      0 < length vs1 →
      array_model t (DfracOwn 1) vs1 -∗
      array_model t (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array_model_persist t dq vs :
      array_model t dq vs ⊢ |==>
      array_model t DfracDiscarded vs.
    Proof.
      apply array_slice_persist.
    Qed.
  End array_model.

  Section array_span.
    Definition array_span t sz i dq n : iProp Σ :=
      ∃ vs,
      ⌜length vs = n⌝ ∗
      array_slice t sz i dq vs.

    Lemma array_span_slice t sz i dq n :
      array_span t sz i dq n ⊢
        ∃ vs,
        ⌜length vs = n⌝ ∗
        array_slice t sz i dq vs.
    Proof.
      iSmash.
    Qed.
    Lemma array_slice_span t sz i dq vs :
      array_slice t sz i dq vs ⊢
      array_span t sz i dq (length vs).
    Proof.
      iSmash.
    Qed.

    Lemma array_span_model t sz i dq n :
      array_span t sz 0 dq sz -∗
        ∃ vs,
        array_model t dq vs.
    Proof.
      iSmash.
    Qed.
    Lemma array_model_span t dq vs :
      array_model t dq vs ⊢
      array_span t (length vs) 0 dq (length vs).
    Proof.
      iSmash.
    Qed.

    #[global] Instance array_span_timeless t sz i dq n :
      Timeless (array_span t sz i dq n).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_span_persistent t sz i n :
      Persistent (array_span t sz i DfracDiscarded n).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_span_fractional t sz i n :
      Fractional (λ q, array_span t sz i (DfracOwn q) n).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%vs & % & (Hslice1 & Hslice2))".
        iSplitL "Hslice1"; iExists vs; auto.
      - iIntros "((%vs & % & Hslice1) & (%_vs & % & Hslice2))".
        iDestruct (array_slice_agree with "Hslice1 Hslice2") as %(_ & <-); [naive_solver.. |].
        iCombine "Hslice1 Hslice2" as "Hslice".
        iExists vs. auto.
    Qed.
    #[global] Instance array_span_as_fractional t sz i q vs :
      AsFractional (array_slice t sz i (DfracOwn q) vs) (λ q, array_slice t sz i (DfracOwn q) vs) q.
    Proof.
      apply _.
    Qed.

    Lemma array_span_agree_size t sz1 i1 dq1 n1 sz2 i2 dq2 n2 :
      array_span t sz1 i1 dq1 n1 -∗
      array_span t sz2 i2 dq2 n2 -∗
      ⌜sz1 = sz2⌝.
    Proof.
      iIntros "(%vs1 & % & Hslice1) (%vs2 & % & Hslice2)".
      iApply (array_slice_agree_size with "Hslice1 Hslice2").
    Qed.

    Lemma array_span_valid t sz i dq n :
      0 < n →
      array_span t sz i dq n ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%vs & % & Hslice)".
      iDestruct (array_slice_valid with "Hslice") as %?; naive_solver.
    Qed.
    Lemma array_span_valid_2 t i sz1 dq1 n1 sz2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      array_span t sz1 i dq1 n1 -∗
      array_span t sz2 i dq2 n2 -∗
      ⌜sz1 = sz2 ∧ ✓ (dq1 ⋅ dq2)⌝.
    Proof.
      iIntros (<- ?) "(%vs1 & % & Hslice1) (%vs2 & % & Hslice2)".
      iDestruct (array_slice_valid_2 with "Hslice1 Hslice2") as %?; naive_solver.
    Qed.
    Lemma array_span_combine t i sz1 dq1 n1 sz2 dq2 n2 :
      n1 = n2 →
      array_span t sz1 i dq1 n1 -∗
      array_span t sz2 i dq2 n2 -∗
        ⌜sz1 = sz2⌝ ∗
        array_span t sz1 i (dq1 ⋅ dq2) n1.
    Proof.
      iIntros "% (%vs & % & Hslice1) (%_vs & % & Hslice2)".
      iDestruct (array_slice_combine with "Hslice1 Hslice2") as "(% & ?)"; first naive_solver.
      iSplit; first iSmash. iExists vs. auto.
    Qed.
    Lemma array_span_dfrac_ne t1 sz1 i1 dq1 n1 t2 sz2 i2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_span t1 sz1 i1 dq1 n1 -∗
      array_span t2 sz2 i2 dq2 n2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      rewrite -not_and_r. iIntros "% % % Hspan1 Hspan2" ((-> & ->)).
      iDestruct (array_span_valid_2 with "Hspan1 Hspan2") as %?; naive_solver.
    Qed.
    Lemma array_span_ne n t1 sz1 i1 n1 t2 sz2 i2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      array_span t1 sz1 i1 (DfracOwn 1) n1 -∗
      array_span t2 sz2 i2 dq2 n2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      intros.
      iApply array_span_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_span_exclusive t i sz1 n1 sz2 n2 :
      n1 = n2 →
      0 < n1 →
      array_span t sz1 i (DfracOwn 1) n1 -∗
      array_span t sz2 i (DfracOwn 1) n2 -∗
      False.
    Proof.
      iIntros "% % (%vs1 & % & Hslice1) (%vs2 & % & Hslice2)".
      iApply (array_slice_exclusive with "Hslice1 Hslice2"); naive_solver.
    Qed.
    Lemma array_span_persist t sz i dq n :
      array_span t sz i dq n ⊢ |==>
      array_span t sz i DfracDiscarded n.
    Proof.
      iIntros "(%vs & % & Hslice)".
      iExists vs. iSplitR; first iSmash.
      iApply array_slice_persist. iSmash+.
    Qed.

    Lemma array_span_app t sz i dq sz1 sz2 :
      array_span t sz i dq sz1 ∗ array_span t sz (i + sz1) dq sz2 ⊣⊢
      array_span t sz i dq (sz1 + sz2).
    Proof.
      iSplit.
      - iIntros "((%vs1 & % & Hslice1) & (%vs2 & % & Hslice2))".
        iExists (vs1 ++ vs2). iSplit; first (rewrite app_length; naive_solver).
        iApply (array_slice_app_1 with "Hslice1 Hslice2"); first done.
      - iIntros "(%vs & % & Hslice)".
        iDestruct (array_slice_app_2 _ _ _ _ _ (take sz1 vs) (drop sz1 vs) with "Hslice") as "(Hslice1 & Hslice2)"; first rewrite take_drop //.
        iSplitL "Hslice1".
        + iExists (take sz1 vs). iFrame. rewrite take_length_le //. lia.
        + iExists (drop sz1 vs). rewrite take_length_le; last lia. iFrame.
          rewrite drop_length. iSmash.
    Qed.
    Lemma array_span_app_1 t sz i dq sz1 sz2 :
      array_span t sz i dq sz1 -∗
      array_span t sz (i + sz1) dq sz2 -∗
      array_span t sz i dq (sz1 + sz2).
    Proof.
      rewrite -array_span_app. iSmash.
    Qed.
    Lemma array_span_app_2 t sz i dq sz1 sz2 sz12 :
      sz12 = sz1 + sz2 →
      array_span t sz i dq sz12 ⊢
        array_span t sz i dq sz1 ∗
        array_span t sz (i + sz1) dq sz2.
    Proof.
      intros ->. rewrite array_span_app //.
    Qed.
  End array_span.

  Lemma array_create_spec :
    {{{ True }}}
      array_create #()
    {{{ t,
      RET t;
      array_model t (DfracOwn 1) []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    iApply wp_fupd.
    wp_apply (chunk_make_spec with "[//]"). iIntros "%l (Hl & _)".
    iDestruct (chunk_model_cons_2 with "Hl") as "(Hsz & Hdata)". rewrite -{1}(Loc.add_0 l).
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iSteps. rewrite Loc.add_0 //.
  Qed.

  Lemma array_make_spec sz v :
    (0 ≤ sz)%Z →
    {{{ True }}}
      array_make #sz v
    {{{ t,
      RET t;
      array_model t (DfracOwn 1) (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    Z_to_nat sz.
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "_".
    wp_smart_apply (chunk_make_spec with "[//]"). iIntros "%l (Hmodel & _)".
    wp_pures.
    rewrite Z.add_1_l -Nat2Z.inj_succ !Nat2Z.id.
    iDestruct (chunk_model_cons with "Hmodel") as "(Hsz & Hmodel)".
    iEval (setoid_rewrite <- (Loc.add_0 l)) in "Hsz". wp_store.
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iExists l. rewrite replicate_length !Loc.add_0. iSmash.
  Qed.

  Lemma array_initi_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "_".
    wp_smart_apply (chunk_make_spec with "[//]"). iIntros "%l (Hmodel & _)".
    wp_pures.
    rewrite Z.add_1_l Z2Nat.inj_succ //.
    iDestruct (chunk_model_cons with "Hmodel") as "(Hsz & Hmodel)".
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    pose Ψ' i (_ : list val) vs := (
      Ψ i vs
    )%I.
    wp_smart_apply (chunk_applyi_spec Ψ' with "[$Hmodel $HΨ]"); rewrite ?replicate_length; first lia.
    { iSteps. iPureIntro.
      erewrite <- (replicate_length (Z.to_nat sz)). eapply lookup_lt_Some. done.
    }
    iIntros "%vs (%Hvs & Hmodel & HΨ)".
    wp_pures.
    iApply ("HΦ" $! #l vs). iFrame. iSteps.
    rewrite !Loc.add_0 -Hvs Z2Nat.id //. iSmash.
  Qed.
  Lemma array_initi_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (Z.to_nat sz - i), Ξ j
    )%I).
    wp_apply (array_initi_spec Ψ' with "[$HΨ Hfn]"); [done | | iSmash].
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (Z.to_nat sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma array_initi_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn #i {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (array_initi_spec Ψ'); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSmash.
  Qed.
  Lemma array_initi_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #i {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (array_initi_spec' Ψ' with "[Hfn]"); [done | | iSmash].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSmash.
  Qed.

  Lemma array_size_spec_atomic_slice t :
    <<<
      True
    | ∀∀ sz i dq vs,
      array_slice t sz i dq vs
    >>>
      array_size t
    <<<
      array_slice t sz i dq vs
    | RET #sz; £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    iApply fupd_wp. iMod "HΦ" as "(%sz & %i & %dq & %vs & (%l & -> & Hslice) & HΦ & _)".
    iMod ("HΦ" with "[Hslice]") as "HΦ"; first iSmash.
    iModIntro. clear.
    wp_rec. wp_pure credit:"H£".
    iMod "HΦ" as "(%sz & %i & %dq & %vs & (%_l & %Heq & #Hsz & Hmodel) & _ & HΦ)". injection Heq as <-.
    wp_load.
    iApply ("HΦ" with "[Hmodel] H£").
    iSmash.
  Qed.
  Lemma array_size_spec_atomic t :
    <<<
      True
    | ∀∀ dq vs,
      array_model t dq vs
    >>>
      array_size t
    <<<
      array_model t dq vs
    | RET #(length vs); £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    awp_apply (array_size_spec_atomic_slice with "[//]").
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%dq %vs Hmodel".
    rewrite /atomic_acc /=. iModIntro. iExists (length vs), 0, dq, vs. iSplitL; iSmash+.
  Qed.
  Lemma array_size_spec_slice t sz i dq vs :
    {{{
      array_slice t sz i dq vs
    }}}
      array_size t
    {{{
      RET #sz;
      array_slice t sz i dq vs
    }}}.
  Proof.
    iSmash.
  Qed.
  Lemma array_size_spec t dq vs :
    {{{
      array_model t dq vs
    }}}
      array_size t
    {{{
      RET #(length vs);
      array_model t dq vs
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma array_unsafe_get_spec_atomic_slice t (i : Z) :
    <<<
      True
    | ∀∀ sz dq vs j v,
      ⌜(j ≤ i)%Z ∧ vs !! Z.to_nat (i - j) = Some v⌝ ∗
      array_slice t sz j dq vs
    >>>
      array_unsafe_get t #i
    <<<
      array_slice t sz j dq vs
    | RET v; £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    iApply fupd_wp. iMod "HΦ" as "(%sz & %dq & %vs & %j & %v & ((%Hj & %Hlookup) & (%l & -> & Hmodel)) & HΦ & _)".
    iMod ("HΦ" with "[Hmodel]") as "HΦ"; first iSmash.
    iModIntro. clear.
    wp_rec. rewrite /array_data. wp_pure credit:"H£". wp_pures.
    iMod "HΦ" as "(%sz & %dq & %vs & %j & %v & ((%Hj & %Hlookup) & (%_l & %Heq & #Hsz & Hmodel)) & _ & HΦ)". injection Heq as <-.
    destruct (Z_of_nat_complete (i - j)) as (k & Hk); first lia.
    assert (i = j + k)%Z as -> by lia.
    rewrite Z.add_simpl_l in Hlookup.
    rewrite -Loc.add_assoc.
    wp_apply (chunk_get_spec with "Hmodel"); [lia | done |]. iIntros "Hmodel".
    iApply ("HΦ" with "[Hmodel] H£"). iSmash.
  Qed.
  Lemma array_unsafe_get_spec_atomic t (i : Z) :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ dq vs v,
      ⌜vs !! Z.to_nat i = Some v⌝ ∗
      array_model t dq vs
    >>>
      array_unsafe_get t #i
    <<<
      array_model t dq vs
    | RET v; £1
    >>>.
  Proof.
    iIntros "%Hi !> %Φ _ HΦ".
    awp_apply (array_unsafe_get_spec_atomic_slice with "[//]").
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%dq %vs %v (%Hlookup & Hmodel)".
    rewrite /atomic_acc /=. iModIntro. iExists (length vs), dq, vs, 0, v. iSplitL.
    { iFrame. rewrite Z.sub_0_r //. }
    rewrite /array_model. iSmash.
  Qed.
  Lemma array_unsafe_get_spec_slice t sz j dq vs (i : Z) v :
    (j ≤ i)%Z →
    vs !! Z.to_nat (i - j) = Some v →
    {{{
      array_slice t sz j dq vs
    }}}
      array_unsafe_get t #i
    {{{
      RET v;
      array_slice t sz j dq vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ Hslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_get_spec_atomic_slice with "[//]").
    rewrite /atomic_acc /=. iExists sz, dq, vs, j, v.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hslice"; first auto. iSplit; first iSmash.
    iIntros "Hslice". iMod "Hclose" as "_". iIntros "!> H£".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hslice").
  Qed.
  Lemma array_unsafe_get_spec t (i : Z) dq vs v :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      array_model t dq vs
    }}}
      array_unsafe_get t #i
    {{{
      RET v;
      array_model t dq vs
    }}}.
  Proof.
    intros. apply array_unsafe_get_spec_slice; first done. rewrite Z.sub_0_r //.
  Qed.

  Lemma array_get_spec_atomic_slice t (i : Z) :
    <<<
      True
    | ∀∀ sz dq vs j v,
      ⌜(j ≤ i)%Z ∧ vs !! Z.to_nat (i - j) = Some v⌝ ∗
      array_slice t sz j dq vs
    >>>
      array_get t #i
    <<<
      array_slice t sz j dq vs
    | RET v; £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "_".
    awp_smart_apply (array_size_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%sz %dq %vs %j %v ((% & %) & Hslice)".
    iAaccIntro with "Hslice"; first iSmash.
    iIntros "Hslice !>". iSplitL; first auto. iIntros "HΦ !> _".
    wp_smart_apply assume_spec'. iIntros "_".
    wp_smart_apply (array_unsafe_get_spec_atomic_slice with "[//] HΦ").
  Qed.
  Lemma array_get_spec_atomic t (i : Z) :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ dq vs v,
      ⌜vs !! Z.to_nat i = Some v⌝ ∗
      array_model t dq vs
    >>>
      array_get t #i
    <<<
      array_model t dq vs
    | RET v; £ 1
    >>>.
  Proof.
    iIntros "%Hi !> %Φ _ HΦ".
    awp_apply (array_get_spec_atomic_slice with "[//]").
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%dq %vs %v (%Hlookup & Hmodel)".
    rewrite /atomic_acc /=. iModIntro. iExists (length vs), dq, vs, 0, v. iSplitL.
    { iFrame. rewrite Z.sub_0_r //. }
    rewrite /array_model. iSmash.
  Qed.
  Lemma array_get_spec_slice t sz j dq vs (i : Z) v :
    (j ≤ i)%Z →
    vs !! Z.to_nat (i - j) = Some v →
    {{{
      array_slice t sz j dq vs
    }}}
      array_get t #i
    {{{
      RET v;
      array_slice t sz j dq vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ Hslice HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "_".
    wp_smart_apply (array_size_spec_slice with "Hslice"). iIntros "Hslice".
    wp_smart_apply assume_spec'. iIntros "_".
    wp_smart_apply (array_unsafe_get_spec_slice with "Hslice"); done.
  Qed.
  Lemma array_get_spec t (i : Z) dq vs v :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      array_model t dq vs
    }}}
      array_get t #i
    {{{
      RET v;
      array_model t dq vs
    }}}.
  Proof.
    intros. apply array_get_spec_slice; first done. rewrite Z.sub_0_r //.
  Qed.

  Lemma array_unsafe_set_spec_atomic_slice t (i : Z) v :
    <<<
      True
    | ∀∀ sz vs j,
      ⌜j ≤ i < j + length vs⌝%Z ∗
      array_slice t sz j (DfracOwn 1) vs
    >>>
      array_unsafe_set t #i v
    <<<
      array_slice t sz j (DfracOwn 1) (<[Z.to_nat (i - j) := v]> vs)
    | RET #(); £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    iApply fupd_wp. iMod "HΦ" as "(%sz & %vs & %j & (%Hi & (%l & -> & Hmodel)) & HΦ & _)".
    iMod ("HΦ" with "[Hmodel]") as "HΦ"; first iSmash.
    iModIntro. clear.
    wp_rec. rewrite /array_data. wp_pure credit:"H£". wp_pures.
    iMod "HΦ" as "(%sz & %vs & %j & (%Hi & (%_l & %Heq & #Hsz & Hmodel)) & _ & HΦ)". injection Heq as <-.
    destruct (Z_of_nat_complete (i - j)) as (k & Hk); first lia.
    assert (i = j + k)%Z as -> by lia.
    rewrite -Loc.add_assoc.
    wp_smart_apply (chunk_set_spec with "Hmodel"); first lia. iIntros "Hmodel".
    iApply ("HΦ" with "[Hmodel] [H£]"); last iSmash.
    rewrite Z.add_simpl_l. iSmash.
  Qed.
  Lemma array_unsafe_set_spec_atomic t (i : Z) v :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs,
      ⌜i < length vs⌝%Z ∗
      array_model t (DfracOwn 1) vs
    >>>
      array_unsafe_set t #i v
    <<<
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    | RET #(); £ 1
    >>>.
  Proof.
    iIntros "%Hi !> %Φ _ HΦ".
    awp_apply (array_unsafe_set_spec_atomic_slice with "[//]").
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs (%Hlookup & Hmodel)".
    rewrite /atomic_acc /=. iModIntro. iExists (length vs), vs, 0. iSplitL.
    { iFrame. rewrite Z.add_0_l //. }
    iSplit; first iSmash. iIntros "Hslisce !>". iRight.
    rewrite Z.sub_0_r /array_model insert_length. auto with iFrame.
  Qed.
  Lemma array_unsafe_set_spec_slice t sz j vs (i : Z) v :
    (j ≤ i < j + length vs)%Z →
    {{{
      array_slice t sz j (DfracOwn 1) vs
    }}}
      array_unsafe_set t #i v
    {{{
      RET #();
      array_slice t sz j (DfracOwn 1) (<[Z.to_nat (i - j) := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ Hslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_set_spec_atomic_slice with "[//]").
    rewrite /atomic_acc /=. iExists sz, vs, j.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hslice"; first auto. iSplit; first iSmash.
    iIntros "Hslice". iMod "Hclose" as "_". iIntros "!> H£".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hslice").
  Qed.
  Lemma array_unsafe_set_spec t (i : Z) vs v :
    (0 ≤ i < length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_unsafe_set t #i v
    {{{
      RET #();
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ Hmodel HΦ".
    wp_apply (array_unsafe_set_spec_slice with "Hmodel"); first done.
    rewrite Z.sub_0_r /array_model insert_length //.
  Qed.

  Lemma array_set_spec_atomic_slice t (i : Z) v :
    <<<
      True
    | ∀∀ sz vs j,
      ⌜(j ≤ i < j + length vs)%Z⌝ ∗
      array_slice t sz j (DfracOwn 1) vs
    >>>
      array_set t #i v
    <<<
      array_slice t sz j (DfracOwn 1) (<[Z.to_nat (i - j) := v]> vs)
    | RET #(); £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "_".
    awp_smart_apply (array_size_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%sz %vs %j (% & Hslice)".
    iAaccIntro with "Hslice"; first iSmash.
    iIntros "Hslice !>". iSplitL; first auto. iIntros "HΦ !> _".
    wp_smart_apply assume_spec'. iIntros "_".
    wp_smart_apply (array_unsafe_set_spec_atomic_slice with "[//] HΦ").
  Qed.
  Lemma array_set_spec_atomic t (i : Z) v :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs,
      ⌜(i < length vs)%Z⌝ ∗
      array_model t (DfracOwn 1) vs
    >>>
      array_set t #i v
    <<<
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    | RET #(); £ 1
    >>>.
  Proof.
    iIntros "%Hi !> %Φ _ HΦ".
    awp_apply (array_set_spec_atomic_slice with "[//]").
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs (%Hi'  & Hmodel)".
    rewrite /atomic_acc /=. iModIntro. iExists (length vs), vs, 0. iSplitL.
    { iFrame. rewrite Z.add_0_l //. }
    iSplit; first iSmash. iIntros "Hslisce !>". iRight.
    rewrite Z.sub_0_r /array_model insert_length. auto with iFrame.
  Qed.
  Lemma array_set_spec_slice t sz j vs (i : Z) v :
    (j ≤ i < j + length vs)%Z →
    {{{
      array_slice t sz j (DfracOwn 1) vs
    }}}
      array_set t #i v
    {{{
      RET #();
      array_slice t sz j (DfracOwn 1) (<[Z.to_nat (i - j) := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ Hslice HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "_".
    wp_smart_apply (array_size_spec_slice with "Hslice"). iIntros "Hslice".
    wp_smart_apply assume_spec'. iIntros "_".
    wp_smart_apply (array_unsafe_set_spec_slice with "Hslice"); done.
  Qed.
  Lemma array_set_spec t (i : Z) vs v :
    (0 ≤ i < length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_set t #i v
    {{{
      RET #();
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ Hmodel HΦ".
    wp_apply (array_set_spec_slice with "Hmodel"); first done.
    rewrite Z.sub_0_r /array_model insert_length //.
  Qed.

  Lemma array_blit_spec_slice_fit t1 sz1 i1 (i1' : Z) dq1 vs1 t2 sz2 i2 (i2' : Z) vs2 (n : Z) :
    i1' = Z.of_nat i1 →
    i2' = Z.of_nat i2 →
    n = length vs1 →
    length vs1 = length vs2 →
    {{{
      array_slice t1 sz1 i1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_blit t1 #i1' t2 #i2' #n
    {{{
      RET #();
      array_slice t1 sz1 i1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> -> -> ?) "%Φ (Hslice1 & Hslice2) HΦ".
    wp_rec. rewrite /array_data.
    wp_smart_apply (array_size_spec_slice with "Hslice1"). iIntros "Hslice1".
    wp_smart_apply (array_size_spec_slice with "Hslice2"). iIntros "Hslice2".
    do 9 (wp_smart_apply assume_spec'; iIntros "_").
    iDestruct "Hslice1" as "(%l1 & -> & #Hsz1 & Hmodel1)".
    iDestruct "Hslice2" as "(%l2 & -> & #Hsz2 & Hmodel2)".
    wp_smart_apply (chunk_copy_spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    iSmash.
  Qed.
  Lemma array_blit_spec_slice t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    (0 ≤ n)%Z →
    (i1 ≤ j1 ≤ i1 + length vs1)%Z →
    (i1 ≤ j1 + n ≤ i1 + length vs1)%Z →
    (i2 ≤ j2 ≤ i2 + length vs2)%Z →
    (i2 ≤ j2 + n ≤ i2 + length vs2)%Z →
    {{{
      array_slice t1 sz1 i1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_blit t1 #j1 t2 #j2 #n
    {{{
      RET #();
      let j1 := Z.to_nat j1 in
      let j2 := Z.to_nat j2 in
      let n := Z.to_nat n in
      array_slice t1 sz1 i1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) (
        take (j2 - i2) vs2 ++
        take n (drop (j1 - i1) vs1) ++
        drop (j2 - i2 + n) vs2
      )
    }}}.
  Proof.
    iIntros "% % % % % %Φ (Hslice1 & Hslice2) HΦ".
    Z_to_nat j1. Z_to_nat j2. Z_to_nat n. rewrite !Nat2Z.id.
    rewrite (Nat.le_add_sub i1 j1); last lia. rewrite (Nat.le_add_sub i2 j2); last lia.
    set k1 := j1 - i1. set k2 := j2 - i2.
    rewrite -{1 2}(take_drop k1 vs1) -{1}(take_drop k2 vs2).
    rewrite -(take_drop n (drop k1 vs1)) -(take_drop n (drop k2 vs2)).
    rewrite !drop_drop.
    iDestruct (array_slice_app_2 with "Hslice1") as "(Hslice11 & Hslice1)"; first done.
    iDestruct (array_slice_app_2 with "Hslice1") as "(Hslice12 & Hslice13)"; first done.
    iDestruct (array_slice_app_2 with "Hslice2") as "(Hslice21 & Hslice2)"; first done.
    iDestruct (array_slice_app_2 with "Hslice2") as "(Hslice22 & Hslice23)"; first done.
    rewrite !take_length !drop_length !Nat.min_l; [| lia..].
    wp_apply (array_blit_spec_slice_fit with "[$Hslice12 $Hslice22]"); try lia.
    { rewrite take_length drop_length. lia. }
    { rewrite !take_length !drop_length. lia. }
    iIntros "(Hslice12 & Hslice22)".
    iApply "HΦ".
    iDestruct (array_slice_app_1 with "Hslice12 Hslice13") as "Hslice1".
    { rewrite take_length drop_length. lia. }
    iDestruct (array_slice_app_1 with "Hslice11 Hslice1") as "$".
    { rewrite take_length. lia. }
    iDestruct (array_slice_app_1 with "Hslice22 Hslice23") as "Hslice2".
    { rewrite take_length drop_length. lia. }
    iDestruct (array_slice_app_1 with "Hslice21 Hslice2") as "Hslice2".
    { rewrite take_length. lia. }
    rewrite -!Nat.le_add_sub //; lia.
  Qed.
  Lemma array_blit_spec t1 (i1 : Z) dq1 vs1 t2 (i2 : Z) vs2 (n : Z) :
    (0 ≤ n)%Z →
    (0 ≤ i1 ≤ length vs1)%Z →
    (0 ≤ i1 + n ≤ length vs1)%Z →
    (0 ≤ i2 ≤ length vs2)%Z →
    (0 ≤ i2 + n ≤ length vs2)%Z →
    {{{
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) vs2
    }}}
      array_blit t1 #i1 t2 #i2 #n
    {{{
      RET #();
      let i1 := Z.to_nat i1 in
      let i2 := Z.to_nat i2 in
      let n := Z.to_nat n in
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) (
        take i2 vs2 ++
        take n (drop i1 vs1) ++
        drop (i2 + n) vs2
      )
    }}}.
  Proof.
    iIntros "% % % % % %Φ (Hmodel1 & Hmodel2) HΦ".
    iDestruct (array_model_slice with "Hmodel1") as "Hslice1".
    iDestruct (array_model_slice with "Hmodel2") as "Hslice2".
    wp_apply (array_blit_spec_slice with "[$Hslice1 $Hslice2]"); [lia.. |]. iIntros "(Hslice1 & Hslice2)".
    rewrite !Nat.sub_0_r.
    iApply "HΦ".
    iDestruct (array_slice_model with "Hslice1") as "$"; first done.
    iDestruct (array_slice_model with "Hslice2") as "$".
    rewrite !app_length !take_length !drop_length. lia.
  Qed.

  Context τ `{!iType (iPropI Σ) τ}.

  Definition array_type (sz : nat) t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    l.[size] ↦□ #sz ∗
    chunk_type τ sz l.[data].
  #[global] Instance array_type_itype sz :
    iType _ (array_type sz).
  Proof.
    split. apply _.
  Qed.

  Lemma array_create_type :
    {{{ True }}}
      array_create #()
    {{{ t,
      RET t; array_type 0 t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    iApply wp_fupd.
    wp_apply (chunk_make_spec with "[//]"). iIntros "%l (Hl & _)".
    iDestruct (chunk_model_cons_2 with "Hl") as "(Hsz & _)".
    rewrite -{1}(Loc.add_0 l). iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iExists l. repeat iSplitR; [iSmash.. |].
    iApply chunk_type_0.
  Qed.

  Lemma array_make_type (sz : Z) v :
    {{{
      τ v
    }}}
      array_make #sz v
    {{{ t,
      RET t; array_type (Z.to_nat sz) t
    }}}.
  Proof.
    iIntros "%Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "%Hsz".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp_smart_apply (chunk_make_spec with "[//]"). iIntros "%l (Hl & _)".
    rewrite Z.add_1_l Z2Nat.inj_succ; last lia. rewrite Nat2Z.id.
    iDestruct (chunk_model_cons_2 with "Hl") as "(Hsz & Hdata)".
    rewrite -{1}(Loc.add_0 l).
    wp_store.
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iExists l. repeat iSplitR; [iSmash.. |].
    iApply inv_alloc. iExists _. iFrame. rewrite replicate_length. iSteps.
    iApply big_sepL_intro. iIntros "%k %_v" ((-> & Hk)%lookup_replicate). iSmash.
  Qed.

  Lemma array_initi_type (sz : Z) fn :
    {{{
      (nat_type --> τ)%T fn
    }}}
      array_initi #sz fn
    {{{ t,
      RET t; array_type (Z.to_nat sz) t
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "%Hsz".
    wp_smart_apply (chunk_make_spec with "[//]"). iIntros "%l (Hmodel & _)".
    rewrite Z.add_1_l Z2Nat.inj_succ //.
    iDestruct (chunk_model_cons with "Hmodel") as "(Hsz & Hmodel)".
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    wp_smart_apply (chunk_applyi_spec_disentangled (λ _, τ) with "[$Hmodel]"); rewrite ?replicate_length; [lia | iSmash |].
    iIntros "%vs (%Hvs & Hmodel & #Hτ)".
    wp_pures.
    iApply "HΦ". iExists l. repeat iSplitR; try iSmash.
    rewrite Loc.add_0 Z2Nat.id //.
  Qed.

  Lemma array_size_type t sz :
    {{{
      array_type sz t
    }}}
      array_size t
    {{{
      RET #sz; True
    }}}.
  Proof.
    iSmash.
  Qed.

  #[local] Lemma array_data_type t sz :
    {{{
      array_type sz t
    }}}
      array_data t
    {{{ l,
      RET #l;
      chunk_type τ sz l
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma array_unsafe_get_type t (sz : nat) (i : Z) :
    (0 ≤ i < sz)%Z →
    {{{
      array_type sz t
    }}}
      array_unsafe_get t #i
    {{{ v,
      RET v; τ v
    }}}.
  Proof.
    iIntros "%Hi %Φ #Ht HΦ".
    wp_rec.
    wp_smart_apply (array_data_type with "Ht"). iIntros "%data #Hdata".
    wp_smart_apply (chunk_get_type with "Hdata"); first done.
    iSmash.
  Qed.

  Lemma array_get_type t sz (i : val) :
    {{{
      array_type sz t ∗
      int_type i
    }}}
      array_get t i
    {{{ v,
      RET v; τ v
    }}}.
  Proof.
    iIntros "%Φ (#Ht & (%i_ & ->)) HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "%Hi".
    wp_smart_apply (array_size_type with "Ht"). iIntros "_".
    wp_smart_apply assume_spec'. iIntros "%Hi'".
    wp_smart_apply (array_unsafe_get_type with "Ht"); first lia.
    iSmash.
  Qed.

  Lemma array_unsafe_set_type t (sz : nat) (i : Z) v :
    (0 ≤ i < sz)%Z →
    {{{
      array_type sz t ∗
      τ v
    }}}
      array_unsafe_set t #i v
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Hi %Φ (#Ht & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (array_data_type with "Ht"). iIntros "%data #Hdata".
    wp_smart_apply (chunk_set_type with "[$Hdata $Hv]"); first done.
    iSmash.
  Qed.

  Lemma array_set_type t sz (i : val) v :
    {{{
      array_type sz t ∗
      int_type i ∗
      τ v
    }}}
      array_set t i v
    {{{
      RET #();  True
    }}}.
  Proof.
    iIntros "%Φ (#Ht & (%i_ & ->) & #Hv) HΦ".
    wp_rec.
    wp_smart_apply assume_spec'. iIntros "%Hi".
    wp_smart_apply (array_size_type with "Ht"). iIntros "_".
    wp_smart_apply assume_spec'. iIntros "%Hi'".
    wp_smart_apply (array_unsafe_set_type with "[$Ht $Hv]"); first lia.
    iSmash.
  Qed.

  Lemma array_blit_type t1 sz1 (i1 : val) t2 sz2 (i2 n : val) :
    {{{
      array_type sz1 t1 ∗
      int_type i1 ∗
      array_type sz2 t2 ∗
      int_type i2 ∗
      int_type n
    }}}
      array_blit t1 i1 t2 i2 n
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Ht1 & (%i1_ & ->) & #Ht2 & (%i2_ & ->) & (%n_ & ->)) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht1"). iIntros "_".
    wp_smart_apply (array_size_type with "Ht2"). iIntros "_".
    do 9 (wp_smart_apply assume_spec'; iIntros "%").
    wp_smart_apply (array_data_type with "Ht2"). iIntros "%data2 Hdata2".
    wp_smart_apply (array_data_type with "Ht1"). iIntros "%data1 Hdata1".
    iDestruct (chunk_type_shift i1_ with "Hdata1") as "Hdata1"; first done.
    iDestruct (chunk_type_shift i2_ with "Hdata2") as "Hdata2"; first done.
    iDestruct (chunk_type_le (Z.to_nat n_) with "Hdata1") as "Hdata1"; first lia.
    wp_smart_apply (chunk_copy_type with "[$Hdata1 $Hdata2]"); [lia.. |].
    iSmash.
  Qed.
End heapGS.

#[global] Opaque array_create.
#[global] Opaque array_make.
#[global] Opaque array_initi.
#[global] Opaque array_size.
#[global] Opaque array_unsafe_get.
#[global] Opaque array_get.
#[global] Opaque array_unsafe_set.
#[global] Opaque array_set.
#[global] Opaque array_blit.

#[global] Opaque array_slice.
#[global] Opaque array_model.
#[global] Opaque array_span.
#[global] Opaque array_type.
