From heap_lang Require Import
  prelude.
From heap_lang.iris.bi Require Import
  big_op.
From heap_lang.language Require Import
  notations
  diaframe.
From heap_lang.std Require Export
  base.
From heap_lang.std Require Import
  assume
  chunk.

Implicit Types i j n : nat.
Implicit Types l : loc.
Implicit Types v t fn : val.
Implicit Types vs : list val.

#[local] Notation "t '.[size]'" :=
  t.[0]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[data]'" :=
  t.[1]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[size]'" :=
  t.[#0]%E
( at level 5
) : expr_scope.
#[local] Notation "t '.[data]'" :=
  t.[#1]%E
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
Definition array_init : val :=
  λ: "sz" "fn",
    array_initi "sz" (λ: <>, "fn" #()).

Definition array_size : val :=
  λ: "t",
    !"t".[size].
#[local] Definition array_data : val :=
  λ: "t",
    "t".[data].

Definition array_unsafe_get : val :=
  λ: "t" "i",
    !(array_data "t").["i"].
Definition array_get : val :=
  λ: "t" "i",
    assume (#0 ≤ "i") ;;
    assume ("i" < array_size "t") ;;
    array_unsafe_get "t" "i".

Definition array_unsafe_set : val :=
  λ: "t" "i" "v",
    (array_data "t").["i"] <- "v".
Definition array_set : val :=
  λ: "t" "i" "v",
    assume (#0 ≤ "i") ;;
    assume ("i" < array_size "t") ;;
    array_unsafe_set "t" "i" "v".

(* array_foldli *)
(* array_foldl *)

(* array_foldri *)
(* array_foldr *)

(* array_iteri *)
(* array_iter *)

(* array_applyi *)
(* array_apply *)

(* array_mapi *)
(* array_map *)

Definition array_blit : val :=
  λ: "t1" "i1" "t2" "i2" "n",
    let: "sz1" := array_size "t1" in
    let: "sz2" := array_size "t2" in
    assume (#0 ≤ "i1") ;;
    assume (#0 ≤ "i2") ;;
    assume (#0 ≤ "n") ;;
    assume ("i1" + "n" ≤ "sz1") ;;
    assume ("i2" + "n" ≤ "sz2") ;;
    chunk_copy (array_data "t1").["i1"] "n" (array_data "t2").["i2"].
Definition array_copy : val :=
  λ: "t1" "t2" "i2",
    array_blit "t1" #0 "t2" "i2" (array_size "t1").

Definition array_grow : val :=
  λ: "t" "sz'" "v'",
    let: "t'" := array_make "sz'" "v'" in
    array_copy "t" "t'" #0 ;;
    "t'".
Definition array_sub : val :=
  λ: "t" "i" "n",
    let: "sz" := array_size "t" in
    assume (#0 ≤ "i") ;;
    assume (#0 ≤ "n") ;;
    assume ("i" + "n" ≤ "sz") ;;
    let: "t'" := array_make "n" #() in
    chunk_copy (array_data "t").["i"] "n" (array_data "t'") ;;
    "t'".
Definition array_shrink : val :=
  λ: "t" "n",
    array_sub "t" #0 "n".
Definition array_clone : val :=
  λ: "t",
    array_shrink "t" (array_size "t").

Definition array_fill_slice : val :=
  λ: "t" "i" "n" "v",
    let: "sz" := array_size "t" in
    assume (#0 ≤ "i") ;;
    assume (#0 ≤ "n") ;;
    assume ("i" + "n" ≤ "sz") ;;
    chunk_fill (array_data "t").["i"] "n" "v".
Definition array_fill : val :=
  λ: "t" "v",
    array_fill_slice "t" #0 (array_size "t") "v".

Section heap_GS.
  Context `{heap_GS : !heapGS Σ}.

  Section array_slice.
    Definition array_slice t (sz : nat) i dq vs : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l.[size] ↦□ #sz ∗
      chunk_model l.[data].[i] dq vs.

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
      - iIntros "(%l & -> & #Hsz & Hmodel1 & Hmodel2)". iSteps.
      - iIntros "((%l & -> & #Hsz & Hmodel1) & (%_l & %Heq & _ & Hmodel2))". injection Heq as <-.
        iExists l. iSteps.
        iApply chunk_model_fractional. iSteps.
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
      iSteps.
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
      iSteps.
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
      iSteps.
    Qed.

    Lemma array_slice_app t sz i dq vs1 vs2 :
      array_slice t sz i dq vs1 ∗
      array_slice t sz (i + length vs1) dq vs2 ⊣⊢
      array_slice t sz i dq (vs1 ++ vs2).
    Proof.
      iSplit.
      - iIntros "((%l & -> & #Hsz & Hmodel1) & (%_l & %Heq & _ & Hmodel2))". injection Heq as <-.
        rewrite Nat2Z.inj_add -Loc.add_assoc.
        iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel"; first done.
        iSteps.
      - iIntros "(%l & -> & #Hsz & Hmodel)".
        iDestruct (chunk_model_app with "Hmodel") as "(Hmodel1 & Hmodel2)".
        iSplitL "Hmodel1"; iExists l; first iSteps.
        rewrite Loc.add_assoc -Nat2Z.inj_add. iSteps.
    Qed.
    Lemma array_slice_app_1 t sz i dq sz1 vs1 vs2 :
      sz1 = length vs1 →
      array_slice t sz i dq vs1 -∗
      array_slice t sz (i + sz1) dq vs2 -∗
      array_slice t sz i dq (vs1 ++ vs2).
    Proof.
      intros ->. rewrite -array_slice_app. iSteps.
    Qed.
    Lemma array_slice_app_2 {t sz i dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      array_slice t sz i dq vs ⊢
        array_slice t sz i dq vs1 ∗
        array_slice t sz (i + length vs1) dq vs2.
    Proof.
      intros ->. rewrite array_slice_app //.
    Qed.

    Lemma array_slice_app3 t sz i dq vs1 vs2 vs3 :
      array_slice t sz i dq vs1 ∗
      array_slice t sz (i + length vs1) dq vs2 ∗
      array_slice t sz (i + length vs1 + length vs2) dq vs3 ⊣⊢
      array_slice t sz i dq (vs1 ++ vs2 ++ vs3).
    Proof.
      rewrite !array_slice_app //.
    Qed.
    Lemma array_slice_app3_1 t sz dq i1 vs1 i2 vs2 i3 vs3 :
      i2 = i1 + length vs1 →
      i3 = i1 + length vs1 + length vs2 →
      array_slice t sz i1 dq vs1 -∗
      array_slice t sz i2 dq vs2 -∗
      array_slice t sz i3 dq vs3 -∗
      array_slice t sz i1 dq (vs1 ++ vs2 ++ vs3).
    Proof.
      intros -> ->. rewrite -array_slice_app3. iSteps.
    Qed.
    Lemma array_slice_app3_2 {t sz i dq vs} vs1 vs2 vs3 :
      vs = vs1 ++ vs2 ++ vs3 →
      array_slice t sz i dq vs ⊢
        array_slice t sz i dq vs1 ∗
        array_slice t sz (i + length vs1) dq vs2 ∗
        array_slice t sz (i + length vs1 + length vs2) dq vs3.
    Proof.
      intros ->. rewrite array_slice_app3 //.
    Qed.

    Lemma array_slice_update {t sz i dq vs} j v :
      vs !! j = Some v →
      array_slice t sz i dq vs ⊢
        array_slice t sz (i + j) dq [v] ∗
        (∀ w, array_slice t sz (i + j) dq [w] -∗ array_slice t sz i dq (<[j := w]> vs)).
    Proof.
      iIntros "%Hlookup Hslice".
      pose proof Hlookup as Hj%lookup_lt_Some.
      pose proof Hlookup as <-%take_drop_middle.
      iDestruct (array_slice_app3_2 _ [v] with "Hslice") as "(Hslice1 & Hslice2 & Hslice3)"; first done.
      setoid_rewrite insert_app_r_alt; rewrite take_length; last lia.
      rewrite Nat.min_l; last lia. rewrite Nat.sub_diag /=.
      iFrame. iIntros "%w Hslice2".
      iApply (array_slice_app3_1 with "Hslice1 Hslice2 Hslice3"); rewrite take_length /=; lia.
    Qed.
    Lemma array_slice_lookup_acc {t sz i dq vs} j v :
      vs !! j = Some v →
      array_slice t sz i dq vs ⊢
        array_slice t sz (i + j) dq [v] ∗
        (array_slice t sz (i + j) dq [v] -∗ array_slice t sz i dq vs).
    Proof.
      iIntros "%Hlookup Hslice".
      iDestruct (array_slice_update with "Hslice") as "(Hv & Hslice)"; first done.
      iSpecialize ("Hslice" $! v). rewrite list_insert_id //. iFrame.
    Qed.
    Lemma array_slice_lookup {t sz i dq vs} j v :
      vs !! j = Some v →
      array_slice t sz i dq vs ⊢
      array_slice t sz (i + j) dq [v].
    Proof.
      intros. rewrite array_slice_lookup_acc //. iSteps.
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
      iSteps.
    Qed.
    Lemma array_model_slice t dq vs :
      array_model t dq vs ⊢
      array_slice t (length vs) 0 dq vs.
    Proof.
      iSteps.
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
      iSteps.
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

    Lemma array_model_update {t dq vs} i v :
      vs !! i = Some v →
      array_model t dq vs ⊢
        array_slice t (length vs) i dq [v] ∗
        (∀ w, array_slice t (length vs) i dq [w] -∗ array_model t dq (<[i := w]> vs)).
    Proof.
      rewrite /array_model. setoid_rewrite insert_length. rewrite -(Nat.add_0_l i).
      apply array_slice_update.
    Qed.
    Lemma array_model_lookup_acc {t dq vs} i v :
      vs !! i = Some v →
      array_model t dq vs ⊢
        array_slice t (length vs) i dq [v] ∗
        (array_slice t (length vs) i dq [v] -∗ array_model t dq vs).
    Proof.
      rewrite /array_model -(Nat.add_0_l i).
      apply array_slice_lookup_acc.
    Qed.
    Lemma array_model_lookup {t dq vs} i v :
      vs !! i = Some v →
      array_model t dq vs ⊢
      array_slice t (length vs) i dq [v].
    Proof.
      rewrite /array_model -(Nat.add_0_l i).
      apply array_slice_lookup.
    Qed.
  End array_model.

  Section array_span.
    Definition array_span t sz i dq n : iProp Σ :=
      ∃ vs,
      ⌜length vs = n⌝ ∗
      array_slice t sz i dq vs.

    Lemma array_span_to_slice t sz i dq n :
      array_span t sz i dq n ⊢
        ∃ vs,
        ⌜length vs = n⌝ ∗
        array_slice t sz i dq vs.
    Proof.
      iSteps.
    Qed.
    Lemma array_slice_to_span t sz i dq vs :
      array_slice t sz i dq vs ⊢
      array_span t sz i dq (length vs).
    Proof.
      iSteps.
    Qed.

    Lemma array_span_to_model t sz i dq n :
      array_span t sz 0 dq sz -∗
        ∃ vs,
        array_model t dq vs.
    Proof.
      iSteps.
    Qed.
    Lemma array_model_to_span t dq vs :
      array_model t dq vs ⊢
      array_span t (length vs) 0 dq (length vs).
    Proof.
      iSteps.
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
      iSplit; first iSteps. iExists vs. auto.
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
      iExists vs. iSplitR; first iSteps.
      iApply array_slice_persist. iSmash+.
    Qed.

    Lemma array_span_app t sz i dq n1 n2 :
      array_span t sz i dq n1 ∗
      array_span t sz (i + n1) dq n2 ⊣⊢
      array_span t sz i dq (n1 + n2).
    Proof.
      iSplit.
      - iIntros "((%vs1 & % & Hslice1) & (%vs2 & % & Hslice2))".
        iExists (vs1 ++ vs2). iSplit; first (rewrite app_length; naive_solver).
        iApply (array_slice_app_1 with "Hslice1 Hslice2"); first done.
      - iIntros "(%vs & % & Hslice)".
        iDestruct (array_slice_app_2 (take n1 vs) (drop n1 vs) with "Hslice") as "(Hslice1 & Hslice2)"; first rewrite take_drop //.
        iSplitL "Hslice1".
        + iExists (take n1 vs). iFrame. rewrite take_length_le //. lia.
        + iExists (drop n1 vs). rewrite take_length_le; last lia. iFrame.
          rewrite drop_length. iSteps.
    Qed.
    Lemma array_span_app_1 t sz i dq n1 n2 :
      array_span t sz i dq n1 -∗
      array_span t sz (i + n1) dq n2 -∗
      array_span t sz i dq (n1 + n2).
    Proof.
      rewrite -array_span_app. iSteps.
    Qed.
    Lemma array_span_app_2 {t sz i dq n} n1 n2 :
      n = n1 + n2 →
      array_span t sz i dq n ⊢
        array_span t sz i dq n1 ∗
        array_span t sz (i + n1) dq n2.
    Proof.
      intros ->. rewrite array_span_app //.
    Qed.

    Lemma array_span_app3 t sz i dq n1 n2 n3 :
      array_span t sz i dq n1 ∗
      array_span t sz (i + n1) dq n2 ∗
      array_span t sz (i + n1 + n2) dq n3 ⊣⊢
      array_span t sz i dq (n1 + n2 + n3).
    Proof.
      iSplit.
      - iIntros "((%vs1 & <- & Hspan1) & (%vs2 & <- & Hspan2) & (%vs3 & <- & Hspan3))".
        iExists (vs1 ++ vs2 ++ vs3). rewrite -array_slice_app3. iFrame.
        rewrite !app_length. iSteps.
      - iIntros "(%vs & %Hvs & Hspan)".
        rewrite -(take_drop n1 vs) -(take_drop n2 (drop n1 vs)) drop_drop.
        iDestruct (array_slice_app3 with "Hspan") as "(Hspan1 & Hspan2 & Hspan3)".
        rewrite !take_length !Nat.min_l; [| rewrite drop_length; lia | lia].
        iSplitL "Hspan1"; last iSplitL "Hspan2".
        all: iExists _; iFrame.
        all: rewrite ?take_length ?drop_length.
        all: iSteps.
    Qed.
    Lemma array_span_app3_1 t sz dq i1 n1 i2 n2 i3 n3 :
      i2 = i1 + n1 →
      i3 = i1 + n1 + n2 →
      array_span t sz i1 dq n1 -∗
      array_span t sz i2 dq n2 -∗
      array_span t sz i3 dq n3 -∗
      array_span t sz i1 dq (n1 + n2 + n3).
    Proof.
      rewrite -array_span_app3. iSteps.
    Qed.
    Lemma array_span_app3_2 {t sz i dq n} n1 n2 n3 :
      n = n1 + n2 + n3 →
      array_span t sz i dq n ⊢
        array_span t sz i dq n1 ∗
        array_span t sz (i + n1) dq n2 ∗
        array_span t sz (i + n1 + n2) dq n3.
    Proof.
      rewrite array_span_app3. iSteps.
    Qed.

    Lemma array_span_update {t sz i dq n} j :
      j < n →
      array_span t sz i dq n ⊢
        ∃ v,
        array_slice t sz (i + j) dq [v] ∗
        (∀ w, array_slice t sz (i + j) dq [w] -∗ array_span t sz i dq n).
    Proof.
      iIntros "%Hj (%vs & %Hv & Hslice)".
      iDestruct (array_slice_update j with "Hslice") as "(Hv & Hslice)".
      { rewrite list_lookup_lookup_total_lt; naive_solver. }
      iExists (vs !!! j). iFrame. iIntros "%w Hw".
      iExists (<[j := w]> vs). iSplit; first rewrite insert_length //.
      iApply ("Hslice" with "Hw").
    Qed.
    Lemma array_span_lookup_acc {t sz i dq n} j :
      j < n →
      array_span t sz i dq n ⊢
        ∃ v,
        array_slice t sz (i + j) dq [v] ∗
        (array_slice t sz (i + j) dq [v] -∗ array_span t sz i dq n).
    Proof.
      iIntros "%Hj Hspan".
      iDestruct (array_span_update with "Hspan") as "(%v & Hv & Hspan)"; first done.
      auto with iFrame.
    Qed.
    Lemma array_span_lookup {t sz i dq n} j :
      j < n →
      array_span t sz i dq n ⊢
        ∃ v,
        array_slice t sz (i + j) dq [v].
    Proof.
      intros. rewrite array_span_lookup_acc //. iSteps.
    Qed.
  End array_span.

  Section array_inv.
    Definition array_inv t (sz : nat) : iProp Σ :=
      ∃ l,
      ⌜t = #l⌝ ∗
      l.[size] ↦□ #sz.

    #[global] Instance array_inv_timeless t sz :
      Timeless (array_inv t sz).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_inv_persistent t sz :
      Persistent (array_inv t sz).
    Proof.
      apply _.
    Qed.

    Lemma array_slice_to_inv t sz i dq vs :
      array_slice t sz i dq vs ⊢
      array_inv t sz.
    Proof.
      iSteps.
    Qed.
    Lemma array_model_to_inv t dq vs :
      array_model t dq vs ⊢
      array_inv t (length vs).
    Proof.
      iSteps.
    Qed.
    Lemma array_span_to_inv t sz i dq n :
      array_span t sz i dq n ⊢
      array_inv t sz.
    Proof.
      iSteps.
    Qed.
  End array_inv.

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
    wp_apply (chunk_make_spec with "[//]") as "%l (Hl & _)".
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
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (chunk_make_spec with "[//]") as "%l (Hmodel & _)".
    wp_pures.
    rewrite Z.add_1_l -Nat2Z.inj_succ !Nat2Z.id.
    iDestruct (chunk_model_cons with "Hmodel") as "(Hsz & Hmodel)".
    iEval (setoid_rewrite <- (Loc.add_0 l)) in "Hsz". wp_store.
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iExists l.
    rewrite replicate_length !Loc.add_0. iSteps.
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
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (chunk_make_spec with "[//]") as "%l (Hmodel & _)".
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
    rewrite !Loc.add_0 -Hvs Z2Nat.id //. iSteps.
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
    wp_apply (array_initi_spec Ψ' with "[$HΨ Hfn]"); [done | | iSteps].
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
    wp_apply (array_initi_spec Ψ'); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
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
    wp_apply (array_initi_spec' Ψ' with "[Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma array_init_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #() {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_initi_spec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma array_init_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #() {{ v, ▷
          Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_initi_spec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma array_init_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn #() {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_init #sz fn
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
    wp_rec.
    wp_smart_apply (array_initi_spec_disentangled Ψ with "[] HΦ"); first done.
    iSteps.
  Qed.
  Lemma array_init_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #() {{ v, ▷
          Ψ i v
        }}
      )
    }}}
      array_init #sz fn
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
    wp_rec.
    wp_smart_apply (array_initi_spec_disentangled' Ψ with "[Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma array_size_spec_inv t sz :
    {{{
      array_inv t sz
    }}}
      array_size t
    {{{
      RET #sz; True
    }}}.
  Proof.
    iSteps.
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
    iMod ("HΦ" with "[Hslice]") as "HΦ"; first iSteps.
    iModIntro. clear.
    wp_rec. wp_pure credit:"H£".
    iMod "HΦ" as "(%sz & %i & %dq & %vs & (%_l & %Heq & #Hsz & Hmodel) & _ & HΦ)". injection Heq as <-.
    wp_load.
    iApply ("HΦ" with "[Hmodel] H£").
    iSteps.
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
    iSteps.
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
    iSteps.
  Qed.

  Lemma array_unsafe_get_spec_atomic_slice t (j : Z) :
    <<<
      True
    | ∀∀ sz dq vs i v,
      ⌜(i ≤ j)%Z ∧ vs !! (Z.to_nat j - i) = Some v⌝ ∗
      array_slice t sz i dq vs
    >>>
      array_unsafe_get t #j
    <<<
      array_slice t sz i dq vs
    | RET v; £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    iApply fupd_wp. iMod "HΦ" as "(%sz & %dq & %vs & %i & %v & ((%Hi & %Hlookup) & (%l & -> & Hmodel)) & HΦ & _)".
    iMod ("HΦ" with "[Hmodel]") as "HΦ"; first iSteps.
    iModIntro. clear.
    wp_rec. rewrite /array_data. wp_pure credit:"H£". wp_pures.
    iMod "HΦ" as "(%sz & %dq & %vs & %i & %v & ((%Hi & %Hlookup) & (%_l & %Heq & #Hsz & Hmodel)) & _ & HΦ)". injection Heq as <-.
    iApply (chunk_get_spec' with "Hmodel"); [lia | done | lia |]. iIntros "!> Hmodel".
    iApply ("HΦ" with "[Hmodel] H£").
    iSteps.
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
    { iFrame. rewrite Nat.sub_0_r //. }
    rewrite /array_model. iSmash.
  Qed.
  Lemma array_unsafe_get_spec_slice k t sz i dq vs (j : Z) v :
    (i ≤ j)%Z →
    vs !! k = Some v →
    k = Z.to_nat j - i →
    {{{
      array_slice t sz i dq vs
    }}}
      array_unsafe_get t #j
    {{{
      RET v;
      array_slice t sz i dq vs
    }}}.
  Proof.
    iIntros (Hj Hlookup ->) "%Φ Hslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_get_spec_atomic_slice with "[//]") without "HΦ".
    rewrite /atomic_acc /=. iExists sz, dq, vs, i, v.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hslice"; first auto. iSplit; first iSteps.
    iIntros "Hslice". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iApply ("HΦ" with "Hslice").
  Qed.
  Lemma array_unsafe_get_spec i_ t (i : Z) dq vs v :
    (0 ≤ i)%Z →
    vs !! i_ = Some v →
    i_ = Z.to_nat i →
    {{{
      array_model t dq vs
    }}}
      array_unsafe_get t #i
    {{{
      RET v;
      array_model t dq vs
    }}}.
  Proof.
    intros Hi Hlookup ->.
    eapply array_unsafe_get_spec_slice; [lia | done | lia].
  Qed.

  Lemma array_get_spec_atomic_slice t (j : Z) :
    <<<
      True
    | ∀∀ sz dq vs i v,
      ⌜(i ≤ j)%Z ∧ vs !! (Z.to_nat j - i) = Some v⌝ ∗
      array_slice t sz i dq vs
    >>>
      array_get t #j
    <<<
      array_slice t sz i dq vs
    | RET v; £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    awp_smart_apply (array_size_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%sz %dq %vs %i %v ((% & %) & Hslice)".
    iAaccIntro with "Hslice"; first iSteps.
    iIntros "Hslice !>". iSplitL; first auto. iIntros "HΦ !> _".
    wp_smart_apply assume_spec' as "_".
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
    { iFrame. rewrite Nat.sub_0_r //. }
    rewrite /array_model. iSmash.
  Qed.
  Lemma array_get_spec_slice k t sz i dq vs (j : Z) v :
    (i ≤ j)%Z →
    vs !! k = Some v →
    k = Z.to_nat j - i →
    {{{
      array_slice t sz i dq vs
    }}}
      array_get t #j
    {{{
      RET v;
      array_slice t sz i dq vs
    }}}.
  Proof.
    iIntros (Hi Hlookup ->) "%Φ Hslice HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_size_spec_slice with "Hslice") as "Hslice".
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_unsafe_get_spec_slice with "Hslice"); done.
  Qed.
  Lemma array_get_spec i_ t (i : Z) dq vs v :
    (0 ≤ i)%Z →
    vs !! i_ = Some v →
    i_ = Z.to_nat i →
    {{{
      array_model t dq vs
    }}}
      array_get t #i
    {{{
      RET v;
      array_model t dq vs
    }}}.
  Proof.
    intros Hi Hlookup ->.
    eapply array_get_spec_slice; [lia | done | lia].
  Qed.

  Lemma array_unsafe_set_spec_atomic_slice t (j : Z) v :
    <<<
      True
    | ∀∀ sz vs i,
      ⌜i ≤ j < i + length vs⌝%Z ∗
      array_slice t sz i (DfracOwn 1) vs
    >>>
      array_unsafe_set t #j v
    <<<
      array_slice t sz i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    | RET #(); £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    iApply fupd_wp. iMod "HΦ" as "(%sz & %vs & %i & (%Hj & (%l & -> & Hmodel)) & HΦ & _)".
    iMod ("HΦ" with "[Hmodel]") as "HΦ"; first iSteps.
    iModIntro. clear.
    wp_rec. rewrite /array_data. wp_pure credit:"H£". wp_pures.
    iMod "HΦ" as "(%sz & %vs & %i & (%Hj & (%_l & %Heq & #Hsz & Hmodel)) & _ & HΦ)". injection Heq as <-.
    iApply (chunk_set_spec' with "Hmodel"); first lia. iIntros "!> Hmodel".
    iApply ("HΦ" with "[Hmodel] [H£]"); last iSteps.
    rewrite Nat2Z.id. iSteps.
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
    iSplit; first iSteps. iIntros "Hslisce !>". iRight.
    rewrite Nat.sub_0_r /array_model insert_length. auto with iFrame.
  Qed.
  Lemma array_unsafe_set_spec_slice t sz i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array_slice t sz i (DfracOwn 1) vs
    }}}
      array_unsafe_set t #j v
    {{{
      RET #();
      array_slice t sz i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hslice HΦ".
    iApply wp_fupd.
    awp_apply (array_unsafe_set_spec_atomic_slice with "[//]") without "HΦ".
    rewrite /atomic_acc /=. iExists sz, vs, i.
    iApply fupd_mask_intro; first done. iIntros "Hclose".
    iSplitL "Hslice"; first auto. iSplit; first iSteps.
    iIntros "Hslice". iMod "Hclose" as "_". iIntros "!> H£ HΦ".
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
    rewrite Nat.sub_0_r /array_model insert_length //.
  Qed.

  Lemma array_set_spec_atomic_slice t (j : Z) v :
    <<<
      True
    | ∀∀ sz vs i,
      ⌜(i ≤ j < i + length vs)%Z⌝ ∗
      array_slice t sz i (DfracOwn 1) vs
    >>>
      array_set t #j v
    <<<
      array_slice t sz i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    | RET #(); £ 1
    >>>.
  Proof.
    iIntros "!> %Φ _ HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    awp_smart_apply (array_size_spec_atomic_slice with "[//]").
    iApply (aacc_aupd_abort with "HΦ"); first done. iIntros "%sz %vs %i (%Hj & Hslice)".
    iAaccIntro with "Hslice"; first iSteps.
    iIntros "Hslice !>". iSplitL; first auto. iIntros "HΦ !> _".
    wp_smart_apply assume_spec' as "_".
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
    iSplit; first iSteps. iIntros "Hslisce !>". iRight.
    rewrite Nat.sub_0_r /array_model insert_length. auto with iFrame.
  Qed.
  Lemma array_set_spec_slice t sz i vs (j : Z) v :
    (i ≤ j < i + length vs)%Z →
    {{{
      array_slice t sz i (DfracOwn 1) vs
    }}}
      array_set t #j v
    {{{
      RET #();
      array_slice t sz i (DfracOwn 1) (<[Z.to_nat j - i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hj %Φ Hslice HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_size_spec_slice with "Hslice") as "Hslice".
    wp_smart_apply assume_spec' as "_".
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
    rewrite Nat.sub_0_r /array_model insert_length //.
  Qed.

  Lemma array_blit_spec_slice_fit t1 sz1 i1 (i1_ : Z) dq1 vs1 t2 sz2 i2 (i2_ : Z) vs2 (n : Z) :
    i1_ = Z.of_nat i1 →
    i2_ = Z.of_nat i2 →
    n = length vs1 →
    length vs1 = length vs2 →
    {{{
      array_slice t1 sz1 i1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_blit t1 #i1_ t2 #i2_ #n
    {{{
      RET #();
      array_slice t1 sz1 i1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> -> -> ?) "%Φ (Hslice1 & Hslice2) HΦ".
    wp_rec. rewrite /array_data.
    wp_smart_apply (array_size_spec_slice with "Hslice1") as "Hslice1".
    wp_smart_apply (array_size_spec_slice with "Hslice2") as "Hslice2".
    repeat (wp_smart_apply assume_spec' as "_").
    iDestruct "Hslice1" as "(%l1 & -> & #Hsz1 & Hmodel1)".
    iDestruct "Hslice2" as "(%l2 & -> & #Hsz2 & Hmodel2)".
    wp_smart_apply (chunk_copy_spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    iSteps.
  Qed.
  Lemma array_blit_spec_slice t1 sz1 i1 (j1 : Z) dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 (n : Z) :
    (i1 ≤ j1)%Z →
    (i2 ≤ j2)%Z →
    (0 ≤ n)%Z →
    (j1 + n ≤ i1 + length vs1)%Z →
    (j2 + n ≤ i2 + length vs2)%Z →
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
    rewrite (Nat.le_add_sub i1 j1); last lia. set k1 := j1 - i1.
    rewrite (Nat.le_add_sub i2 j2); last lia. set k2 := j2 - i2.
    rewrite -{1 2}(take_drop k1 vs1) -(take_drop n (drop k1 vs1)).
    rewrite -{1}(take_drop k2 vs2) -(take_drop n (drop k2 vs2)).
    rewrite !drop_drop.
    iDestruct (array_slice_app3_2 with "Hslice1") as "(Hslice11 & Hslice12 & Hslice13)"; first done.
    iDestruct (array_slice_app3_2 with "Hslice2") as "(Hslice21 & Hslice22 & Hslice23)"; first done.
    rewrite !take_length !drop_length !Nat.min_l; [| lia..].
    wp_apply (array_blit_spec_slice_fit with "[$Hslice12 $Hslice22]") as "(Hslice12 & Hslice22)"; try lia.
    { rewrite take_length drop_length. lia. }
    { rewrite !take_length !drop_length. lia. }
    iApply "HΦ".
    iDestruct (array_slice_app3_1 with "Hslice11 Hslice12 Hslice13") as "$"; [rewrite !take_length ?drop_length; lia.. |].
    iDestruct (array_slice_app3_1 with "Hslice21 Hslice22 Hslice23") as "Hslice2"; [rewrite !take_length ?drop_length; lia.. |].
    rewrite -!Nat.le_add_sub //; lia.
  Qed.
  Lemma array_blit_spec t1 (i1 : Z) dq1 vs1 t2 (i2 : Z) vs2 (n : Z) :
    (0 ≤ i1)%Z →
    (0 ≤ i2)%Z →
    (0 ≤ n)%Z →
    (i1 + n ≤ length vs1)%Z →
    (i2 + n ≤ length vs2)%Z →
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
    wp_apply (array_blit_spec_slice with "[$Hslice1 $Hslice2]") as "(Hslice1 & Hslice2)"; [lia.. |].
    rewrite !Nat.sub_0_r.
    iApply "HΦ".
    iDestruct (array_slice_model with "Hslice1") as "$"; first done.
    iDestruct (array_slice_model with "Hslice2") as "$".
    rewrite !app_length !take_length !drop_length. lia.
  Qed.

  Lemma array_copy_spec_slice_fit t1 dq1 vs1 t2 sz2 i2 (i2_ : Z) vs2 :
    i2_ = Z.of_nat i2 →
    length vs1 = length vs2 →
    {{{
      array_model t1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_copy t1 t2 #i2_
    {{{
      RET #();
      array_model t1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs1
    }}}.
  Proof.
    iIntros (-> ?) "%Φ (Hmodel1 & Hslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_apply (array_blit_spec_slice_fit with "[$Hmodel1 $Hslice2]"); [done.. |].
    iSteps.
  Qed.
  Lemma array_copy_spec_slice t1 dq1 vs1 t2 sz2 i2 (j2 : Z) vs2 :
    (i2 ≤ j2)%Z →
    (j2 + length vs1 ≤ i2 + length vs2)%Z →
    {{{
      array_model t1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) vs2
    }}}
      array_copy t1 t2 #j2
    {{{
      RET #();
      array_model t1 dq1 vs1 ∗
      array_slice t2 sz2 i2 (DfracOwn 1) (
        take (Z.to_nat j2 - i2) vs2 ++
        vs1 ++
        drop (Z.to_nat j2 - i2 + length vs1) vs2
      )
    }}}.
  Proof.
    iIntros "% % %Φ (Hmodel1 & Hslice2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_apply (array_blit_spec_slice with "[$Hmodel1 $Hslice2]"); [lia.. |].
    rewrite Nat2Z.id firstn_all /=. iSteps.
  Qed.
  Lemma array_copy_spec t1 dq1 vs1 t2 (i2 : Z) vs2 :
    (0 ≤ i2)%Z →
    (i2 + length vs1 ≤ length vs2)%Z →
    {{{
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) vs2
    }}}
      array_copy t1 t2 #i2
    {{{
      RET #();
      array_model t1 dq1 vs1 ∗
      array_model t2 (DfracOwn 1) (
        take (Z.to_nat i2) vs2 ++
        vs1 ++
        drop (Z.to_nat i2 + length vs1) vs2
      )
    }}}.
  Proof.
    iIntros "% % %Φ (Hmodel1 & Hmodel2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel1") as "Hmodel1".
    wp_apply (array_blit_spec with "[$Hmodel1 $Hmodel2]"); [lia.. |].
    rewrite Nat2Z.id firstn_all /=. iSteps.
  Qed.

  Lemma array_grow_spec t dq vs sz' v' :
    (length vs ≤ sz')%Z →
    {{{
      array_model t dq vs
    }}}
      array_grow t #sz' v'
    {{{ t',
      RET t';
      array_model t' (DfracOwn 1) (vs ++ replicate (Z.to_nat sz' - length vs) v')
    }}}.
  Proof.
    iIntros "%Hsz' %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (array_make_spec with "[//]") as "%t' Hmodel'"; first lia.
    wp_smart_apply (array_copy_spec with "[$Hmodel $Hmodel']"); first done.
    { rewrite replicate_length. lia. }
    rewrite drop_replicate. iSteps.
  Qed.

  Lemma array_sub_spec_slice_fit t sz dq vs i (i_ n : Z) :
    i_ = Z.of_nat i →
    n = length vs →
    {{{
      array_slice t sz i dq vs
    }}}
      array_sub t #i_ #n
    {{{ t',
      RET t';
      array_slice t sz i dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) vs)
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (%l & -> & #Hsz & Hmodel) HΦ".
    wp_rec. rewrite /array_size /array_data. wp_load.
    repeat (wp_smart_apply assume_spec' as "_").
    wp_smart_apply (array_make_spec with "[//]") as "%t' (%l' & -> & #Hsz' & Hmodel')"; first lia.
    iEval (rewrite Loc.add_0) in "Hmodel'".
    wp_smart_apply (chunk_copy_spec with "[$Hmodel $Hmodel']") as "(Hmodel & Hmodel')"; first lia.
    { rewrite replicate_length //. }
    wp_pures.
    iApply "HΦ". iSplitL "Hmodel"; first iSteps. iExists l'.
    rewrite replicate_length take_length Nat2Z.id Nat.min_id !Loc.add_0 firstn_all. iSteps.
  Qed.
  Lemma array_sub_spec_slice t sz dq vs i (j n : Z) :
    (i ≤ j)%Z →
    (0 ≤ n)%Z →
    (j + n ≤ i + length vs)%Z →
    {{{
      array_slice t sz i dq vs
    }}}
      array_sub t #j #n
    {{{ t',
      RET t';
      array_slice t sz i dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) (drop (Z.to_nat j - Z.to_nat i) vs))
    }}}.
  Proof.
    iIntros "% % % %Φ Hslice HΦ".
    Z_to_nat j. Z_to_nat n. rewrite !Nat2Z.id.
    rewrite (Nat.le_add_sub i j); last lia. set k := j - i.
    rewrite -{1 2}(take_drop k vs) -(take_drop n (drop k vs)).
    rewrite !drop_drop.
    iDestruct (array_slice_app3_2 with "Hslice") as "(Hslice1 & Hslice2 & Hslice3)"; first done.
    rewrite !take_length !drop_length !Nat.min_l; [| lia..].
    wp_apply (array_sub_spec_slice_fit with "Hslice2") as "%t' (Hslice2 & Hmodel')"; try lia.
    { rewrite take_length drop_length. lia. }
    iApply "HΦ".
    iDestruct (array_slice_app3_1 with "Hslice1 Hslice2 Hslice3") as "$"; [rewrite !take_length ?drop_length; lia.. |].
    rewrite Nat2Z.id take_take Nat.min_id -Nat.le_add_sub //. lia.
  Qed.
  Lemma array_sub_spec t dq vs (i n : Z) :
    (0 ≤ i)%Z →
    (0 ≤ n)%Z →
    (i + n ≤ length vs)%Z →
    {{{
      array_model t dq vs
    }}}
      array_sub t #i #n
    {{{ t',
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) (drop (Z.to_nat i) vs))
    }}}.
  Proof.
    iIntros "% % % %Φ Hmodel HΦ".
    wp_apply (array_sub_spec_slice with "Hmodel"); [done.. |].
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  Lemma array_shrink_spec t dq vs (n : Z) :
    (0 ≤ n ≤ length vs)%Z →
    {{{
      array_model t dq vs
    }}}
      array_shrink t #n
    {{{ t',
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) (take (Z.to_nat n) vs)
    }}}.
  Proof.
    iIntros "%Hn %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (array_sub_spec with "Hmodel"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_clone_spec t dq vs :
    {{{
      array_model t dq vs
    }}}
      array_clone t
    {{{ t',
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_apply (array_shrink_spec with "Hmodel") as "%t' (Hmodel & Hmodel')"; first lia.
    rewrite firstn_all2; last lia.
    iApply ("HΦ" with "[$Hmodel $Hmodel']").
  Qed.

  Lemma array_fill_slice_spec t sz vs i (i_ n : Z) v :
    i_ = Z.of_nat i →
    n = length vs →
    {{{
      array_slice t sz i (DfracOwn 1) vs
    }}}
      array_fill_slice t #i_ #n v
    {{{
      RET #();
      array_slice t sz i (DfracOwn 1) (replicate (Z.to_nat n) v)
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (%l & -> & #Hsz & Hmodel) HΦ".
    wp_rec. rewrite /array_size /array_data.
    wp_load.
    repeat (wp_smart_apply assume_spec' as "_").
    wp_smart_apply (chunk_fill_spec with "Hmodel"); first lia.
    iSteps.
  Qed.

  Lemma array_fill_spec t vs v :
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_fill t v
    {{{
      RET #();
      array_model t (DfracOwn 1) (replicate (length vs) v)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_apply (array_fill_slice_spec with "Hmodel") as "model"; [lia | done |].
    iApply "HΦ".
    rewrite Nat2Z.id -{1}(replicate_length (length vs) v) //.
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
      RET t;
      array_type 0 t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    iApply wp_fupd.
    wp_apply (chunk_make_spec with "[//]") as "%l (Hl & _)".
    iDestruct (chunk_model_cons_2 with "Hl") as "(Hsz & _)".
    rewrite -{1}(Loc.add_0 l). iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iExists l. repeat iSplitR; [iSteps.. |].
    iApply chunk_type_0.
  Qed.

  Lemma array_make_type sz v :
    {{{
      τ v
    }}}
      array_make #sz v
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      array_type (Z.to_nat sz) t
    }}}.
  Proof.
    iIntros "%Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp_smart_apply (chunk_make_spec with "[//]") as "%l (Hl & _)".
    rewrite Z.add_1_l Z2Nat.inj_succ; last lia. rewrite Nat2Z.id.
    iDestruct (chunk_model_cons_2 with "Hl") as "(Hsz & Hdata)".
    rewrite -{1}(Loc.add_0 l).
    wp_store.
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iStep. iExists l. repeat iSplitR; [iSteps.. |].
    iApply inv_alloc. iExists _. iFrame. rewrite replicate_length. iSteps.
    iApply big_sepL_intro. iIntros "%k %_v" ((-> & Hk)%lookup_replicate). iSteps.
  Qed.

  Lemma array_initi_type sz fn :
    {{{
      (nat_type --> τ)%T fn
    }}}
      array_initi #sz fn
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      array_type (Z.to_nat sz) t
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (chunk_make_spec with "[//]") as "%l (Hmodel & _)".
    rewrite Z.add_1_l Z2Nat.inj_succ //.
    iDestruct (chunk_model_cons with "Hmodel") as "(Hsz & Hmodel)".
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    wp_smart_apply (chunk_applyi_spec_disentangled (λ _, τ) with "[$Hmodel]"); rewrite ?replicate_length; [lia | iSteps |].
    iIntros "%vs (%Hvs & Hmodel & #Hτ)".
    wp_pures.
    iApply "HΦ". iStep. iExists l. repeat iSplitR; try iSteps.
    rewrite Loc.add_0 Z2Nat.id //.
  Qed.

  Lemma array_init_type sz fn :
    {{{
      (unit_type --> τ)%T fn
    }}}
      array_init #sz fn
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      array_type (Z.to_nat sz) t
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply (array_initi_type with "[] HΦ").
    iSteps.
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
    iSteps.
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
    iSteps.
  Qed.

  Lemma array_unsafe_get_type t (sz : nat) (i : Z) :
    (0 ≤ i < sz)%Z →
    {{{
      array_type sz t
    }}}
      array_unsafe_get t #i
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Hi %Φ #Ht HΦ".
    wp_rec.
    wp_smart_apply (array_data_type with "Ht") as "%data #Hdata".
    wp_smart_apply (chunk_get_type with "Hdata"); first done.
    iSteps.
  Qed.

  Lemma array_get_type t sz (i : Z) :
    {{{
      array_type sz t
    }}}
      array_get t #i
    {{{ v,
      RET v;
      ⌜0 ≤ i < sz⌝%Z ∗
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Ht HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hi".
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_smart_apply assume_spec' as "%Hi'".
    wp_smart_apply (array_unsafe_get_type with "Ht"); first lia.
    iSteps.
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
    wp_smart_apply (array_data_type with "Ht") as "%data #Hdata".
    wp_smart_apply (chunk_set_type with "[$Hdata $Hv]"); first done.
    iSteps.
  Qed.

  Lemma array_set_type t sz (i : Z) v :
    {{{
      array_type sz t ∗
      τ v
    }}}
      array_set t #i v
    {{{
      RET #();
      ⌜0 ≤ i < sz⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Ht & #Hv) HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hi".
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_smart_apply assume_spec' as "%Hi'".
    wp_smart_apply (array_unsafe_set_type with "[$Ht $Hv]"); first lia.
    iSteps.
  Qed.

  Lemma array_blit_type t1 sz1 (i1 : Z) t2 sz2 (i2 n : Z) :
    {{{
      array_type sz1 t1 ∗
      array_type sz2 t2
    }}}
      array_blit t1 #i1 t2 #i2 #n
    {{{
      RET #();
      ⌜0 ≤ i1 ∧ 0 ≤ i2 ∧ 0 ≤ n ∧ i1 + n ≤ sz1 ∧ i2 + n ≤ sz2⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Ht1 & #Ht2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht1") as "_".
    wp_smart_apply (array_size_type with "Ht2") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_data_type with "Ht2") as "%data2 Hdata2".
    wp_smart_apply (array_data_type with "Ht1") as "%data1 Hdata1".
    iDestruct (chunk_type_shift i1 with "Hdata1") as "Hdata1"; first lia.
    iDestruct (chunk_type_shift i2 with "Hdata2") as "Hdata2"; first lia.
    iDestruct (chunk_type_le (Z.to_nat n) with "Hdata1") as "Hdata1"; first lia.
    wp_smart_apply (chunk_copy_type with "[$Hdata1 $Hdata2]"); [lia.. |].
    iSteps.
  Qed.

  Lemma array_copy_type t1 sz1 t2 sz2 (i2 : Z) :
    {{{
      array_type sz1 t1 ∗
      array_type sz2 t2
    }}}
      array_copy t1 t2 #i2
    {{{
      RET #();
      ⌜0 ≤ i2 ∧ i2 + sz1 ≤ sz2⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Ht1 & #Ht2) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht1") as "_".
    wp_apply array_blit_type; first iFrame "#∗".
    iSteps.
  Qed.

  Lemma array_grow_type t sz sz' v' :
    {{{
      array_type sz t ∗
      τ v'
    }}}
      array_grow t #sz' v'
    {{{ t',
      RET t';
      ⌜sz ≤ sz'⌝ ∗
      array_type (Z.to_nat sz') t'
    }}}.
  Proof.
    iIntros "%Φ (#Ht & #Hv') HΦ".
    wp_rec.
    wp_smart_apply (array_make_type with "Hv'") as "%t' (_ & #Ht')".
    wp_smart_apply (array_copy_type with "[]") as "(_ & %Hsz')"; first iFrame "#∗".
    wp_pures.
    iApply ("HΦ" with "[$Ht']").
    iSteps.
  Qed.

  Lemma array_sub_type t sz (i n : Z) :
    {{{
      array_type sz t
    }}}
      array_sub t #i #n
    {{{ t',
      RET t';
      ⌜0 ≤ i ∧ 0 ≤ n ∧ i + n ≤ sz⌝%Z ∗
      array_type (Z.to_nat n) t'
    }}}.
  Proof.
    iIntros "%Φ #Ht HΦ".
    wp_rec. rewrite {2}/array_data.
    wp_smart_apply (array_size_type with "Ht") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_make_spec with "[//]") as "%t' (%l' & -> & #Hsz' & Hdata')"; first done.
    wp_smart_apply (array_data_type with "Ht") as "%data Hdata".
    iDestruct (chunk_type_shift i with "Hdata") as "Hdata"; first lia.
    iDestruct (chunk_type_le (Z.to_nat n) with "Hdata") as "Hdata"; first lia.
    iEval (rewrite Loc.add_0) in "Hdata'".
    wp_smart_apply (chunk_copy_type' with "[$Hdata $Hdata']"); first lia.
    { rewrite replicate_length //. }
    rewrite replicate_length. iSteps.
  Qed.

  Lemma array_shrink_type t sz (n : Z) :
    {{{
      array_type sz t
    }}}
      array_shrink t #n
    {{{ t',
      RET t';
      ⌜0 ≤ n ≤ sz⌝%Z ∗
      array_type (Z.to_nat n) t'
    }}}.
  Proof.
    iIntros "%Φ Ht HΦ".
    wp_rec.
    wp_smart_apply (array_sub_type with "Ht").
    iSteps.
  Qed.

  Lemma array_clone_type t sz :
    {{{
      array_type sz t
    }}}
      array_clone t
    {{{ t',
      RET t';
      array_type sz t'
    }}}.
  Proof.
    iIntros "%Φ #Ht HΦ".
    wp_rec.
    wp_apply (array_size_type with "Ht") as "_".
    wp_smart_apply (array_shrink_type with "Ht").
    rewrite Nat2Z.id. iSteps.
  Qed.

  Lemma array_fill_slice_type t sz (i n : val) v :
    {{{
      array_type sz t ∗
      int_type i ∗
      int_type n ∗
      τ v
    }}}
      array_fill_slice t i n v
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Ht & (%i_ & ->) & (%n_ & ->) & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    repeat (wp_smart_apply assume_spec' as "%").
    wp_smart_apply (array_data_type with "Ht") as "%l Hl".
    iDestruct (chunk_type_shift i_ with "Hl") as "Hl"; first lia.
    iDestruct (chunk_type_le (Z.to_nat n_) with "Hl") as "Hl"; first lia.
    wp_smart_apply (chunk_fill_type with "[$Hl $Hv] HΦ"); first lia.
  Qed.

  Lemma array_fill_type t sz v :
    {{{
      array_type sz t ∗
      τ v
    }}}
      array_fill t v
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Ht & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (array_size_type with "Ht") as "_".
    wp_apply (array_fill_slice_type with "[$Ht] HΦ"); first iSteps.
  Qed.
End heap_GS.

#[global] Opaque array_create.
#[global] Opaque array_make.
#[global] Opaque array_initi.
#[global] Opaque array_init.
#[global] Opaque array_size.
#[global] Opaque array_unsafe_get.
#[global] Opaque array_get.
#[global] Opaque array_unsafe_set.
#[global] Opaque array_set.
#[global] Opaque array_blit.
#[global] Opaque array_copy.
#[global] Opaque array_grow.
#[global] Opaque array_sub.
#[global] Opaque array_shrink.
#[global] Opaque array_clone.
#[global] Opaque array_fill_slice.
#[global] Opaque array_fill.

#[global] Opaque array_slice.
#[global] Opaque array_model.
#[global] Opaque array_span.
#[global] Opaque array_inv.
#[global] Opaque array_type.
