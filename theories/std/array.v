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
  chunk.

Section heapGS.
Context `{!heapGS Σ}.

  Implicit Types i n : nat.
  Implicit Types l : loc.
  Implicit Types v t fn : val.
  Implicit Types vs : list val.

  Notation "t '.[size]'" := t.[0]%stdpp
( at level 5
  ) : stdpp_scope.
  Notation "t '.[data]'" := t.[1]%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.[size]'" := t.[0]%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.[data]'" := t.[1]%E
  ( at level 5
  ) : expr_scope.

  Definition array_create : val :=
    λ: <>,
      chunk_make #1 #0.

  Definition array_make : val :=
    λ: "sz" "v",
      if: "sz" < #0 then (
        diverge #()
      ) else (
        let: "t" := chunk_make ("sz" + #1) "v" in
        "t".[size] <- "sz" ;;
        "t"
      ).

  Definition array_init : val :=
    λ: "sz" "fn",
      if: "sz" < #0 then (
        diverge #()
      ) else (
        chunk_init ("sz" + #1) (λ: "i",
          if: "i" = #0 then "sz" else "fn" ("i" - #1)
        )
      ).

  Definition array_size : val :=
    λ: "t",
      !"t".[size].

  Definition array_unsafe_get : val :=
    λ: "t" "i",
      !("t".[data] +ₗ "i").
  Definition array_get : val :=
    λ: "t" "i",
      if: (#0 ≤ "i") && ("i" < array_size "t") then (
        array_unsafe_get "t" "i"
      ) else (
        diverge #()
      ).

  Definition array_unsafe_set : val :=
    λ: "t" "i" "v",
      "t".[data] +ₗ "i" <- "v".
  Definition array_set : val :=
    λ: "t" "i" "v",
      if: (#0 ≤ "i") && ("i" < array_size "t") then (
        array_unsafe_set "t" "i" "v"
      ) else (
        diverge #()
      ).

  Section array_inv.
    Definition array_inv t (sz : nat) : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l.[size] ↦□ #sz.

    #[global] Instance array_inv_persistent t sz :
      Persistent (array_inv t sz).
    Proof.
      apply _.
    Qed.
  End array_inv.

  Section array_model.
    Definition array_model t dq vs : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l.[size] ↦□ #(length vs) ∗
      chunk_model l.[data] dq vs.

    Lemma array_model_inv t dq vs :
      array_model t dq vs ⊢
      array_inv t (length vs).
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
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & #Hsz & Hmodel1 & Hmodel2)". iSmash.
      - iIntros "((%l & -> & #Hsz & Hmodel1) & (%_l & %Heq & _ & Hmodel2))". injection Heq as <-.
        iExists l. iFrame "#". iSplit; first iSmash.
        iApply chunk_model_fractional. iSmash.
    Qed.
    #[global] Instance array_model_as_fractional t q vs :
      AsFractional (array_model t (DfracOwn q) vs) (λ q, array_model t (DfracOwn q) vs) q.
    Proof.
      split; done || apply _.
    Qed.

    Lemma array_inv_model_valid t sz dq vs :
      array_inv t sz -∗
      array_model t dq vs -∗
      ⌜length vs = sz⌝.
    Proof.
      iSmash.
    Qed.

    Lemma array_model_valid t dq vs :
      0 < length vs →
      array_model t dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%l & -> & #Hsz & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first done.
    Qed.
    Lemma array_model_combine t dq1 vs1 dq2 vs2 :
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
        array_model t (dq1 ⋅ dq2) vs1 ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "(%l & -> & #Hsz & Hmodel1) (%_l & %Heq & #_Hsz & Hmodel2)". injection Heq as <-.
      iDestruct (mapsto_agree with "Hsz _Hsz") as %[= ?%(inj _)]. iClear "_Hsz".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & <-)"; first done.
      iSmash.
    Qed.
    Lemma array_model_valid_2 t dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & ->)".
      iDestruct (array_model_valid with "Hmodel") as %?; done.
    Qed.
    Lemma array_model_agree t dq1 vs1 dq2 vs2 :
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "Hmodel1 Hmodel2".
      iDestruct (array_model_combine with "Hmodel1 Hmodel2") as "(_ & ->)". iSmash.
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
      iIntros "(%l & -> & #Hsz & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iSmash.
    Qed.
  End array_model.

  Section array_slice.
    Definition array_slice t i dq vs : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      chunk_model (l.[data] +ₗ i) dq vs.

    Lemma array_slice_model t dq vs sz :
      sz = length vs →
      array_inv t sz -∗
      array_slice t 0 dq vs -∗
      array_model t dq vs.
    Proof.
      iIntros (->) "(%l & -> & #Hsz) (%_l & %Heq & Hmodel)". injection Heq as <-.
      iExists l. rewrite !Loc.add_0. iSmash.
    Qed.
    Lemma array_model_slice t dq vs :
      array_model t dq vs ⊢
      array_slice t 0 dq vs.
    Proof.
      iIntros "(%l & -> & #Hsz & Hmodel)".
      iExists l. rewrite !Loc.add_0. iSmash.
    Qed.

    #[global] Instance array_slice_timeless t i dq vs :
      Timeless (array_slice t i dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_slice_persistent t i vs :
      Persistent (array_slice t i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_slice_fractional t i vs :
      Fractional (λ q, array_slice t i (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & Hmodel1 & Hmodel2)". iSmash.
      - iIntros "((%l & -> & Hmodel1) & (%_l & %Heq & Hmodel2))". injection Heq as <-.
        iExists l. iSplit; first iSmash.
        iApply chunk_model_fractional. iSmash.
    Qed.
    #[global] Instance array_slice_as_fractional t i q vs :
      AsFractional (array_slice t i (DfracOwn q) vs) (λ q, array_slice t i (DfracOwn q) vs) q.
    Proof.
      split; done || apply _.
    Qed.

    Lemma array_slice_valid t i dq vs :
      0 < length vs →
      array_slice t i dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%l & -> & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first done.
    Qed.
    Lemma array_slice_combine t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array_slice t i dq1 vs1 -∗
      array_slice t i dq2 vs2 -∗
        array_slice t i (dq1 ⋅ dq2) vs1 ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% (%l & -> & Hmodel1) (%_l & %Heq & Hmodel2)". injection Heq as <-.
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & <-)"; first done.
      iSmash.
    Qed.
    Lemma array_slice_valid_2 t i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_slice t i dq1 vs1 -∗
      array_slice t i dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (array_slice_combine with "Hmodel1 Hmodel2") as "(Hmodel & ->)"; first done.
      iDestruct (array_slice_valid with "Hmodel") as %?; done.
    Qed.
    Lemma array_slice_agree t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array_slice t i dq1 vs1 -∗
      array_slice t i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_slice_combine with "Hmodel1 Hmodel2") as "(_ & ->)"; done.
    Qed.
    Lemma array_slice_dfrac_ne t1 i1 dq1 vs1 t2 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_slice t1 i1 dq1 vs1 -∗
      array_slice t2 i2 dq2 vs2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      rewrite -not_and_r. iIntros "% % % Hmodel1 Hmodel2" ((-> & ->)).
      iDestruct (array_slice_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array_slice_ne t1 i1 vs1 t2 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_slice t1 i1 (DfracOwn 1) vs1 -∗
      array_slice t2 i2 dq2 vs2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      intros. iApply array_slice_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_slice_exclusive t i vs1 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_slice t i (DfracOwn 1) vs1 -∗
      array_slice t i (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (array_slice_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array_slice_persist t i dq vs :
      array_slice t i dq vs ⊢ |==>
      array_slice t i DfracDiscarded vs.
    Proof.
      iIntros "(%l & -> & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iSmash.
    Qed.

    Lemma array_slice_app t i dq vs1 vs2 :
      array_slice t i dq vs1 ∗ array_slice t (i + length vs1) dq vs2 ⊣⊢
      array_slice t i dq (vs1 ++ vs2).
    Proof.
      iSplit.
      - iIntros "((%l & -> & Hmodel1) & (%_l & %Heq & Hmodel2))". injection Heq as <-.
        rewrite Nat2Z.inj_add -Loc.add_assoc.
        iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel"; first done.
        iSmash.
      - iIntros "(%l & -> & Hmodel)".
        iDestruct (chunk_model_app with "Hmodel") as "(Hmodel1 & Hmodel2)".
        iSplitL "Hmodel1"; iExists l; first iSmash.
        rewrite Loc.add_assoc -Nat2Z.inj_add. iSmash.
    Qed.
    Lemma array_slice_app_1 t i dq vs1 vs2 sz :
      sz = length vs1 →
      array_slice t i dq vs1 -∗
      array_slice t (i + sz) dq vs2 -∗
      array_slice t i dq (vs1 ++ vs2).
    Proof.
      intros ->. rewrite -array_slice_app. iSmash.
    Qed.
    Lemma array_slice_app_2 t i dq vs vs1 vs2 :
      vs = vs1 ++ vs2 →
      array_slice t i dq vs ⊢
        array_slice t i dq vs1 ∗
        array_slice t (i + length vs1) dq vs2.
    Proof.
      intros ->. rewrite array_slice_app //.
    Qed.
  End array_slice.

  Section array_span.
    Definition array_span t i dq n : iProp Σ :=
      ∃ vs,
      ⌜length vs = n⌝ ∗
      array_slice t i dq vs.

    Lemma array_span_slice t i dq n :
      array_span t i dq n ⊢
        ∃ vs,
        ⌜length vs = n⌝ ∗
        array_slice t i dq vs.
    Proof.
      iSmash.
    Qed.
    Lemma array_slice_span t i dq vs :
      array_slice t i dq vs ⊢
      array_span t i dq (length vs).
    Proof.
      iSmash.
    Qed.

    Lemma array_span_model t i dq n sz :
      array_inv t sz -∗
      array_span t 0 dq sz -∗
      ∃ vs, array_model t dq vs.
    Proof.
      rewrite array_span_slice. iIntros "#Hinv (%vs & <- & Hslice)".
      iExists vs. iApply array_slice_model; done.
    Qed.
    Lemma array_model_span t dq vs :
      array_model t dq vs ⊢
      array_span t 0 dq (length vs).
    Proof.
      rewrite -array_slice_span -array_model_slice //.
    Qed.

    #[global] Instance array_span_timeless t i dq n :
      Timeless (array_span t i dq n).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_span_persistent t i n :
      Persistent (array_span t i DfracDiscarded n).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_span_fractional t i n :
      Fractional (λ q, array_span t i (DfracOwn q) n).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%vs & % & (Hslice1 & Hslice2))".
        iSplitL "Hslice1"; iExists vs; auto.
      - iIntros "((%vs & % & Hslice1) & (%_vs & % & Hslice2))".
        iDestruct (array_slice_agree with "Hslice1 Hslice2") as %<-; [naive_solver.. |].
        iCombine "Hslice1 Hslice2" as "Hslice".
        iExists vs. auto.
    Qed.
    #[global] Instance array_span_as_fractional t i q vs :
      AsFractional (array_slice t i (DfracOwn q) vs) (λ q, array_slice t i (DfracOwn q) vs) q.
    Proof.
      apply _.
    Qed.

    Lemma array_span_valid t i dq n :
      0 < n →
      array_span t i dq n ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%vs & % & Hslice)".
      iDestruct (array_slice_valid with "Hslice") as %?; naive_solver.
    Qed.
    Lemma array_span_valid_2 t i dq1 n1 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      array_span t i dq1 n1 -∗
      array_span t i dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝.
    Proof.
      iIntros (<- ?) "(%vs1 & % & Hslice1) (%vs2 & % & Hslice2)".
      iDestruct (array_slice_valid_2 with "Hslice1 Hslice2") as "($ & _)"; naive_solver.
    Qed.
    Lemma array_span_combine t i dq1 n1 dq2 n2 :
      n1 = n2 →
      array_span t i dq1 n1 -∗
      array_span t i dq2 n2 -∗
      array_span t i (dq1 ⋅ dq2) n1.
    Proof.
      iIntros "% (%vs & % & Hslice1) (%_vs & % & Hslice2)".
      iDestruct (array_slice_combine with "Hslice1 Hslice2")as "(Hslice & _)"; first naive_solver.
      iExists vs. auto.
    Qed.
    Lemma array_span_dfrac_ne i t1 dq1 n1 t2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_span t1 i dq1 n1 -∗
      array_span t2 i dq2 n2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      iIntros "% % % Hspan1 Hspan2". iIntros (->).
      iDestruct (array_span_valid_2 with "Hspan1 Hspan2") as %?; naive_solver.
    Qed.
    Lemma array_span_ne i n t1 n1 t2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      array_span t1 i (DfracOwn 1) n1 -∗
      array_span t2 i dq2 n2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      intros. iApply array_span_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_span_exclusive t i n1 n2 :
      n1 = n2 →
      0 < n1 →
      array_span t i (DfracOwn 1) n1 -∗
      array_span t i (DfracOwn 1) n2 -∗
      False.
    Proof.
      iIntros "% % (%vs1 & % & Hslice1) (%vs2 & % & Hslice2)".
      iApply (array_slice_exclusive with "Hslice1 Hslice2"); naive_solver.
    Qed.
    Lemma array_span_persist t i dq n :
      array_span t i dq n ⊢ |==>
      array_span t i DfracDiscarded n.
    Proof.
      iIntros "(%vs & % & Hslice)".
      iExists vs. iSplitR; first iSmash. iApply array_slice_persist. done.
    Qed.

    Lemma array_span_app t i dq sz1 sz2 :
      array_span t i dq sz1 ∗ array_span t (i + sz1) dq sz2 ⊣⊢
      array_span t i dq (sz1 + sz2).
    Proof.
      iSplit.
      - iIntros "((%vs1 & % & Hslice1) & (%vs2 & % & Hslice2))".
        iExists (vs1 ++ vs2). iSplit; first (rewrite app_length; naive_solver).
        iApply (array_slice_app_1 with "Hslice1 Hslice2"); first done.
      - iIntros "(%vs & % & Hslice)".
        iDestruct (array_slice_app_2 _ _ _ _ (take sz1 vs) (drop sz1 vs) with "Hslice") as "(Hslice1 & Hslice2)"; first rewrite take_drop //.
        iSplitL "Hslice1".
        + iExists (take sz1 vs). iFrame. rewrite take_length_le //. lia.
        + iExists (drop sz1 vs). rewrite take_length_le; last lia. iFrame.
          rewrite drop_length. iSmash.
    Qed.
    Lemma array_span_app_1 t i dq sz1 sz2 :
      array_span t i dq sz1 -∗
      array_span t (i + sz1) dq sz2 -∗
      array_span t i dq (sz1 + sz2).
    Proof.
      rewrite -array_span_app. iSmash.
    Qed.
    Lemma array_span_app_2 t i dq sz sz1 sz2 :
      sz = sz1 + sz2 →
      array_span t i dq sz ⊢
        array_span t i dq sz1 ∗
        array_span t (i + sz1) dq sz2.
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
    wp_apply (chunk_make_spec with "[//]"); first lia. iIntros "%l (Hl & _)".
    iDestruct (chunk_model_cons_2 with "Hl") as "(Hsz & Hdata)". rewrite -{1}(Loc.add_0 l).
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iSmash.
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
    wp_rec. wp_pures.
    rewrite bool_decide_eq_false_2; last lia. wp_pures.
    wp_apply (chunk_make_spec with "[//]"); first lia. iIntros "%l (Hmodel & _)".
    wp_pures.
    rewrite Z.add_1_r -Nat2Z.inj_succ !Nat2Z.id.
    iDestruct (chunk_model_cons with "Hmodel") as "(Hsz & Hmodel)".
    iEval (setoid_rewrite <- (Loc.add_0 l)) in "Hsz". wp_store.
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iExists l. rewrite replicate_length. iSmash.
  Qed.

  Lemma array_init_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ [] ∗
      [∗ list] i ∈ seq 0 (Z.to_nat sz), ∀ vs_done,
        ⌜i = length vs_done⌝ -∗
        Ψ vs_done -∗
        WP fn #(i : nat) {{ v, Ψ (vs_done ++ [v]) }}
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "% %Φ (HΨ & Hfn) HΦ".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp_rec. wp_pures.
    rewrite bool_decide_eq_false_2; last lia. wp_pures.
    iApply wp_fupd.
    pose Ψ' vs := (
      match vs with
      | [] => Ψ []
      | v :: vs => ⌜v = #sz⌝ ∗ Ψ vs
      end
    )%I.
    wp_smart_apply (chunk_init_spec Ψ' with "[$HΨ Hfn]"); first lia.
    { rewrite Z.add_1_r -Nat2Z.inj_succ Nat2Z.id (seq_app 1 sz) /=. iSplitR.
      - iIntros (vs_done ->%symmetry%nil_length_inv) "HΨ'".
        wp_pures.
        naive_solver.
      - iApply (big_sepL_mono_strong' with "Hfn"); first rewrite !seq_length //. iIntros "!>" (i ? ? ((-> & _)%lookup_seq & (-> & _)%lookup_seq)) "Hfn %vs_done %Hi HΨ'".
        wp_pures.
        rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ /=.
        destruct vs_done as [| v vs_done]; first iSmash.
        iDestruct "HΨ'" as "(-> & HΨ)".
        iApply (wp_wand with "(Hfn [] HΨ)"); first naive_solver. iIntros "%v HΨ".
        naive_solver.
    }
    iIntros "%l %vs (%Hvs & Hmodel & HΨ' & _)".
    destruct vs as [| v vs]; first (simpl in Hvs; lia).
    iDestruct (chunk_model_cons with "Hmodel") as "(Hsz & Hmodel)". rewrite -{1}(Loc.add_0 l).
    iMod (mapsto_persist with "Hsz") as "#Hsz". iModIntro.
    iDestruct "HΨ'" as "(-> & HΨ)".
    iApply ("HΦ" $! _ vs). iFrame.
    iSplit. { list_simplifier. auto with lia. }
    iExists l. iFrame. iSplit; first iSmash.
    assert (length vs = sz) as -> by (simpl in Hvs; lia). iSmash.
  Qed.
  Lemma array_init_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ [] ∗
      ∀ i vs_done,
      {{{ ⌜i = length vs_done ∧ i < Z.to_nat sz⌝ ∗ Ψ vs_done }}}
        fn #i
      {{{ v, RET v; Ψ (vs_done ++ [v]) }}}
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "% %Φ (HΨ & #Hfn) HΦ".
    wp_apply (array_init_spec Ψ with "[$HΨ]"); try done.
    iApply big_sepL_intro. iIntros "!> %i %_i %H_i %vs_done % HΨ". apply lookup_seq in H_i as (-> & ?).
    iApply ("Hfn" with "[$HΨ]"); iSmash.
  Qed.
  Lemma array_init_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #(i : nat) {{ Ψ i }}
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ([∗ list] i ↦ v ∈ vs, Ψ i v)
    }}}.
  Proof.
    iIntros "% %Φ Hfn HΦ".
    set (Ψ' vs := ([∗ list] i ↦ v ∈ vs, Ψ i v)%I).
    wp_apply (array_init_spec Ψ' with "[Hfn]"); try done.
    iSplit; first rewrite /Ψ' //.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v % Hfn %vs_done -> HΨ'".
    iApply (wp_wand with "Hfn"). iIntros "%v HΨ". iFrame. iSplitL; last iSmash.
    rewrite right_id //.
  Qed.
  Lemma array_init_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ∀ i,
      {{{ ⌜i < Z.to_nat sz⌝ }}}
        fn #i
      {{{ v, RET v; Ψ i v }}}
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ([∗ list] i ↦ v ∈ vs, Ψ i v)
    }}}.
  Proof.
    iIntros "% %Φ #Hfn HΦ".
    wp_apply array_init_spec_disentangled; try done.
    iApply big_sepL_intro. iIntros "!> %i %_i %Hlookup".
    apply lookup_seq in Hlookup as (-> & ?).
    iApply ("Hfn" with "[//]"). iSmash.
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
  Lemma array_size_spec' t sz :
    {{{
      array_inv t sz
    }}}
      array_size t
    {{{
      RET #sz; True
    }}}.
  Proof.
    iSmash.
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
    iIntros "% % %Φ (%l & -> & #Hsz & Hmodel) HΦ".
    wp_rec.
    wp_smart_apply (chunk_get_spec with "Hmodel"); [done.. |].
    iSmash.
  Qed.
  Lemma array_unsafe_get_spec' t (j : nat) dq vs (i : Z) v :
    (j ≤ i)%Z →
    vs !! Z.to_nat (i - j) = Some v →
    {{{
      array_slice t j dq vs
    }}}
      array_unsafe_get t #i
    {{{
      RET v;
      array_slice t j dq vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ (%l & -> & Hmodel) HΦ".
    destruct (Z_of_nat_complete (i - j)) as (k & Hk); first lia.
    assert (i = j + k)%Z as -> by lia.
    rewrite Z.add_simpl_l in Hlookup.
    wp_rec. wp_pures.
    rewrite -Loc.add_assoc.
    wp_apply (chunk_get_spec with "Hmodel"); [lia | done |].
    iSmash.
  Qed.
  Lemma array_unsafe_get_spec_atomic t (i : Z) :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ dq vs v,
      array_model t dq vs ∗
      ⌜vs !! Z.to_nat i = Some v⌝
    >>>
      array_unsafe_get t #i
    <<<
      array_model t dq vs
    | RET v; True
    >>>.
  Proof.
    iIntros "%Hi !> %Φ _ HΦ".
    iApply fupd_wp. iMod "HΦ" as "(%dq & %vs & %v & ((%l & -> & Hmodel) & %Hlookup) & HΦ & _)".
    iMod ("HΦ" with "[Hmodel]") as "HΦ"; first iSmash.
    iModIntro. clear- Hi.
    wp_rec. wp_pures.
    iMod "HΦ" as "(%dq & %vs & %v & ((%_l & %Heq & #Hsz & Hmodel) & %Hlookup) & _ & HΦ)". injection Heq as <-.
    wp_smart_apply (chunk_get_spec with "Hmodel"); [done.. |]. iIntros "Hmodel".
    iApply ("HΦ" with "[Hmodel] [//]"). iSmash.
  Qed.
  Lemma array_unsafe_get_spec_atomic' t (i : Z) :
    <<<
      True
    | ∀∀ dq vs j v,
      array_slice t j dq vs ∗
      ⌜(j ≤ i)%Z ∧ vs !! Z.to_nat (i - j) = Some v⌝
    >>>
      array_unsafe_get t #i
    <<<
      array_slice t j dq vs
    | RET v; True
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    iApply fupd_wp. iMod "HΦ" as "(%dq & %vs & %j & %v & ((%l & -> & Hmodel) & (%Hj & %Hlookup)) & HΦ & _)".
    iMod ("HΦ" with "[Hmodel]") as "HΦ"; first iSmash.
    iModIntro. clear.
    wp_rec. wp_pures.
    iMod "HΦ" as "(%dq & %vs & %j & %v & ((%_l & %Heq & Hmodel) & (%Hj & %Hlookup)) & _ & HΦ)". injection Heq as <-.
    destruct (Z_of_nat_complete (i - j)) as (k & Hk); first lia.
    assert (i = j + k)%Z as -> by lia.
    rewrite Z.add_simpl_l in Hlookup.
    rewrite -Loc.add_assoc.
    wp_smart_apply (chunk_get_spec with "Hmodel"); [lia | done |]. iIntros "Hmodel".
    iApply ("HΦ" with "[Hmodel] [//]"). iSmash.
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
    iIntros "% % %Φ Hmodel HΦ".
    wp_rec. wp_pures.
    case_bool_decide; last wp_smart_apply wp_diverge.
    wp_smart_apply (array_size_spec with "Hmodel"). iIntros "Hmodel".
    wp_pures.
    case_bool_decide; last wp_smart_apply wp_diverge.
    wp_smart_apply (array_unsafe_get_spec with "Hmodel"); iSmash+.
  Qed.
  Lemma array_get_spec' t sz (j : nat) dq vs (i : Z) v :
    (j ≤ i)%Z →
    vs !! Z.to_nat (i - j) = Some v →
    {{{
      array_inv t sz ∗
      array_slice t j dq vs
    }}}
      array_get t #i
    {{{
      RET v;
      array_slice t j dq vs
    }}}.
  Proof.
    iIntros "% % %Φ (#Hinv & Hslice) HΦ".
    wp_rec. wp_pures.
    case_bool_decide; last wp_smart_apply wp_diverge.
    wp_smart_apply (array_size_spec' with "Hinv"). iIntros "_".
    wp_pures.
    case_bool_decide; last wp_smart_apply wp_diverge.
    wp_smart_apply (array_unsafe_get_spec' with "Hslice"); iSmash+.
  Qed.
  Lemma array_get_spec_atomic t (i : Z) :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ dq vs v,
      array_model t dq vs ∗
      ⌜vs !! Z.to_nat i = Some v⌝
    >>>
      array_get t #i
    <<<
      array_model t dq vs
    | RET v; True
    >>>.
  Proof.
    iIntros "%Hi !> %Φ _ HΦ".
    iApply fupd_wp. iMod "HΦ" as "(%dq & %vs & %v & (Hmodel & %Hlookup) & HΦ & _)".
    iDestruct (array_model_inv with "Hmodel") as "#Hinv".
    iMod ("HΦ" with "[$Hmodel]") as "HΦ"; first iSmash.
    iModIntro. remember (length vs) as sz. clear- Hi.
    wp_rec. wp_pures.
    case_bool_decide; last wp_smart_apply wp_diverge.
    wp_smart_apply (array_size_spec' with "Hinv"). iIntros "_".
    wp_pures.
    case_bool_decide; last wp_smart_apply wp_diverge.
    wp_smart_apply (array_unsafe_get_spec_atomic with "[//]"); iSmash+.
  Qed.
  Lemma array_get_spec_atomic' t sz (i : Z) :
    <<<
      array_inv t sz
    | ∀∀ dq vs j v,
      array_slice t j dq vs ∗
      ⌜(j ≤ i)%Z ∧ vs !! Z.to_nat (i - j) = Some v⌝
    >>>
      array_get t #i
    <<<
      array_slice t j dq vs
    | RET v; True
    >>>.
  Proof.
    iIntros "!> %Φ #Hinv HΦ".
    wp_rec. wp_pures.
    case_bool_decide; last wp_smart_apply wp_diverge.
    wp_smart_apply (array_size_spec' with "Hinv"). iIntros "_".
    wp_pures.
    case_bool_decide; last wp_smart_apply wp_diverge.
    wp_smart_apply (array_unsafe_get_spec_atomic' with "[//]"); iSmash+.
  Qed.

  Context τ `{!iType (iPropI Σ) τ}.

  Definition array_type t : iProp Σ :=
    ∃ l (sz : nat),
    ⌜t = #l⌝ ∗
    l.[size] ↦□ #sz ∗
    inv nroot (
      ∃ vs,
      ⌜sz = length vs⌝ ∗
      chunk_model l.[data] (DfracOwn 1) vs ∗ [∗list] v ∈ vs, τ v
    ).
  #[global] Instance array_type_itype :
    iType _ array_type.
  Proof.
    intros ?. apply _.
  Qed.

  Lemma array_create_spec_type :
    {{{ True }}}
      array_create #()
    {{{ t,
      RET t; array_type t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    iApply wp_fupd.
    wp_apply (chunk_make_spec with "[//]"); first lia. iIntros "%l (Hl & _)".
    iDestruct (chunk_model_cons_2 with "Hl") as "(Hsz & _)".
    rewrite -{1}(Loc.add_0 l). iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iExists l, 0. repeat iSplitR; [iSmash.. |].
    iApply inv_alloc. iExists []. iSmash.
  Qed.

  Lemma array_make_spec_type sz v :
    {{{
      int_type sz ∗
      τ v
    }}}
      array_make sz v
    {{{ t,
      RET t; array_type t
    }}}.
  Proof.
    iIntros "%Φ ((%sz_ & ->) & #Hv) HΦ".
    wp_rec. wp_pures.
    case_bool_decide; first wp_smart_apply wp_diverge.
    Z_to_nat sz_ as sz.
    wp_smart_apply (chunk_make_spec with "[//]"); first lia. iIntros "%l (Hl & _)".
    rewrite Z2Nat.inj_succ; last lia. rewrite Nat2Z.id.
    iDestruct (chunk_model_cons_2 with "Hl") as "(Hsz & Hdata)".
    rewrite -{1}(Loc.add_0 l).
    wp_store.
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iExists l, _. repeat iSplitR; [iSmash.. |].
    iApply inv_alloc. iExists _. iFrame. rewrite replicate_length. iSteps.
    iApply big_sepL_intro. iIntros "%k %_v" ((-> & Hk)%lookup_replicate). iSmash.
  Qed.

  Lemma array_init_spec_type sz fn :
    {{{
      int_type sz ∗
      function_type nat_type τ fn
    }}}
      array_init sz fn
    {{{ t,
      RET t; array_type t
    }}}.
  Proof.
    iIntros "%Φ ((%sz_ & ->) & #Hfn) HΦ".
    wp_rec. wp_pures.
    case_bool_decide; first wp_smart_apply wp_diverge.
    Z_to_nat sz_ as sz.
    iApply wp_fupd.
    pose (Ψ vs := (
      match vs with
      | [] => emp
      | v :: vs => ⌜v = #sz⌝ ∗ [∗list] w ∈ vs, τ w
      end
    )%I).
    wp_smart_apply (chunk_init_spec' Ψ); first lia.
    { clear Φ. iSplit; first iSmash.
      iIntros ([| i] [| v vs]) "!> %Φ ((%Hi & _) & HΨ) HΦ"; try done; first iSmash.
      iDestruct "HΨ" as "(-> & Hvs)".
      wp_pures.
      iApply (wp_wand with "(Hfn [])"); first iSmash. iIntros "%w Hw".
      iApply "HΦ". iFrame. iSmash.
    }
    iIntros "%l %vs (%Hvs & Hmodel & HΨ & _)".
    destruct vs as [| v vs]; first (simpl in Hvs; lia).
    iDestruct (chunk_model_cons with "Hmodel") as "(Hsz & Hmodel)". rewrite -{1}(Loc.add_0 l).
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    iDestruct "HΨ" as "(-> & HΨ)".
    iApply "HΦ". iExists l, sz. repeat iSplitR; [iSmash.. |].
    iApply inv_alloc. iExists vs. iFrame.
    assert (length vs = sz) as -> by (simpl in Hvs; lia). iSmash.
  Qed.

  Lemma array_size_spec_type t :
    {{{
      array_type t
    }}}
      array_size t
    {{{ sz,
      RET #sz;
      array_inv t sz
    }}}.
  Proof.
    iSmash.
  Qed.

  Lemma array_unsafe_get_spec_type t (sz : nat) (i : Z) :
    (0 ≤ i < sz)%Z →
    {{{
      array_inv t sz ∗
      array_type t
    }}}
      array_unsafe_get t #i
    {{{ v,
      RET v; τ v
    }}}.
  Proof.
    iIntros "%Hi %Φ ((%l & -> & #Hsz) & (%_l & %_sz & %Heq & #_Hsz & #Hinv)) HΦ". injection Heq as <-.
    iDestruct (mapsto_agree with "Hsz _Hsz") as %[= <-%(inj _)]. iClear "_Hsz".
    wp_rec. wp_pures.
    iInv "Hinv" as "(%vs & >-> & >Hmodel & #Hvs)".
    edestruct (lookup_lt_is_Some_2 vs (Z.to_nat i)) as (v & Hlookup); first lia.
    iApply (chunk_get_spec with "Hmodel"); [lia | done |].
    iIntros "!> Hmodel !>". iSplitR "HΦ"; first iSmash.
    iApply "HΦ".
    iApply (big_sepL_lookup with "Hvs"). done.
  Qed.

  Lemma array_get_spec_type t (i : val) :
    {{{
      array_type t ∗
      int_type i
    }}}
      array_get t i
    {{{ v,
      RET v; τ v
    }}}.
  Proof.
    iIntros "%Φ (#Htype & (%i_ & ->)) HΦ".
    wp_rec. wp_pures.
    case_bool_decide; last wp_smart_apply wp_diverge.
    wp_smart_apply (array_size_spec_type with "Htype"). iIntros "%sz #Hinv".
    wp_pures.
    case_bool_decide; last wp_smart_apply wp_diverge.
    wp_smart_apply (array_unsafe_get_spec_type with "[$Hinv $Htype]"); first lia.
    iSmash.
  Qed.
End heapGS.

#[global] Opaque array_create.
#[global] Opaque array_make.
#[global] Opaque array_init.
#[global] Opaque array_size.
#[global] Opaque array_unsafe_get.
#[global] Opaque array_get.
#[global] Opaque array_unsafe_set.
#[global] Opaque array_set.
