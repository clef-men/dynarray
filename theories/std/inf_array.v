From Coq.Logic Require Import
  FunctionalExtensionality.

From heap_lang Require Import
  prelude.
From heap_lang.iris.base_logic Require Import
  lib.auth_excl.
From heap_lang.language Require Import
  notations
  proofmode.
From heap_lang.std Require Export
  base.
From heap_lang.std Require Import
  record3
  array
  mutex.

Implicit Types l : loc.
Implicit Types v t : val.
Implicit Types us : list val.
Implicit Types vs : nat → val.

#[local] Notation "t '.[data]'" :=
  t.[0]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[default]'" :=
  t.[1]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[mutex]'" :=
  t.[2]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[data]'" :=
  t.[#0]%E
( at level 5
) : expr_scope.
#[local] Notation "t '.[default]'" :=
  t.[#1]%E
( at level 5
) : expr_scope.
#[local] Notation "t '.[mutex]'" :=
  t.[#2]%E
( at level 5
) : expr_scope.

Class InfArrayG Σ `{heap_GS : !heapGS Σ} (mutex : mutex Σ) := {
  #[local] inf_array_G_model_G :: AuthExclG Σ (nat -d> valO) ;
}.

Definition inf_array_Σ := #[
  auth_excl_Σ (nat -d> valO)
].
#[global] Instance subG_inf_array_Σ Σ `{heap_GS : !heapGS Σ} mutex :
  subG inf_array_Σ Σ →
  InfArrayG Σ mutex.
Proof.
  solve_inG.
Qed.

Section inf_array_G.
  Context `{heap_GS : !heapGS Σ} mutex `{inf_array_G : !InfArrayG Σ mutex}.

  Definition inf_array_create : val :=
    λ: "default",
      let: "data" := array_create #() in
      let: "t" := record3_make "data" "default" #() in
      let: "mtx" := mutex.(mutex_create) #() in
      "t".[mutex] <- "mtx" ;;
      "t".

  Definition inf_array_get : val :=
    λ: "t" "i",
      mutex.(mutex_protect) !"t".[mutex] (λ: <>,
        let: "data" := !"t".[data] in
        if: "i" < array_size "data" then (
          array_unsafe_get "data" "i"
        ) else (
          !"t".[default]
        )
      ).

  Definition inf_array_set : val :=
    λ: "t" "i" "v",
      mutex.(mutex_protect) !"t".[mutex] (λ: <>,
        let: "data" := !"t".[data] in
        let: "sz" := array_size "data" in
        if: "i" < "sz" then (
          array_unsafe_set "data" "i" "v"
        ) else (
          let: "data" := array_grow "data" (#1 + "i") !"t".[default] in
          "t".[data] <- "data" ;;
          array_unsafe_set "data" "i" "v"
        )
      ).

  #[local] Definition inf_array_inv_inner l γ default : iProp Σ :=
    ∃ data us vs,
    l.[data] ↦ data ∗
    array_model data (DfracOwn 1) us ∗
    auth_excl_frag γ vs ∗
    ⌜vs = λ i, if decide (i < length us) then us !!! i else default⌝.
  Definition inf_array_inv t : iProp Σ :=
    ∃ l γ default mtx,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[mutex] ↦□ mtx ∗
    l.[default] ↦□ default ∗
    mutex.(mutex_inv) mtx (inf_array_inv_inner l γ default).

  Definition inf_array_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    auth_excl_auth γ (DfracOwn 1) vs.
  Definition inf_array_model' t vsₗ vsᵣ :=
    inf_array_model t (
      λ i,
        if decide (i < length vsₗ) then vsₗ !!! i else vsᵣ (i - length vsₗ)
    ).

  #[global] Instance inf_array_inv_persistent t :
    Persistent (inf_array_inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_array_model_ne t n :
    Proper (pointwise_relation nat (=) ==> (≡{n}≡)) (inf_array_model t).
  Proof.
    intros vs1 vs2 ->%functional_extensionality. done.
  Qed.
  #[global] Instance inf_array_model_proper t :
    Proper (pointwise_relation nat (=) ==> (≡)) (inf_array_model t).
  Proof.
    intros vs1 vs2 Hvs. rewrite equiv_dist. solve_proper.
  Qed.
  #[global] Instance inf_array_model_timeless t vs :
    Timeless (inf_array_model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_array_model'_ne t n :
    Proper ((=) ==> pointwise_relation nat (=) ==> (≡{n}≡)) (inf_array_model' t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance inf_array_model'_proper t :
    Proper ((=) ==> pointwise_relation nat (=) ==> (≡)) (inf_array_model' t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance inf_array_model'_timeless t vsₗ vsᵣ :
    Timeless (inf_array_model' t vsₗ vsᵣ).
  Proof.
    apply _.
  Qed.

  Lemma inf_array_model'_shift t vsₗ v vsᵣ :
    inf_array_model' t (vsₗ ++ [v]) vsᵣ ⊣⊢
    inf_array_model' t vsₗ (λ i, match i with 0 => v | S i => vsᵣ i end).
  Proof.
    rewrite /inf_array_model' inf_array_model_proper; first done.
    intros j. rewrite app_length /=.
    destruct (Nat.lt_total j (length vsₗ)) as [| [-> |]].
    - rewrite !decide_True; try lia.
      rewrite lookup_total_app_l //.
    - rewrite decide_True; last lia.
      rewrite decide_False; last lia.
      rewrite lookup_total_app_r //.
      rewrite Nat.sub_diag //.
    - rewrite !decide_False; try lia.
      case_match; [lia | f_equal; lia].
  Qed.
  Lemma inf_array_model'_shift_r t vsₗ v vsᵣ :
    inf_array_model' t (vsₗ ++ [v]) vsᵣ ⊢
    inf_array_model' t vsₗ (λ i, match i with 0 => v | S i => vsᵣ i end).
  Proof.
    rewrite inf_array_model'_shift. iSteps.
  Qed.
  Lemma inf_array_model'_shift_l t vsₗ vsᵣ v vsᵣ' :
    (∀ i, vsᵣ i = match i with 0 => v | S i => vsᵣ' i end) →
    inf_array_model' t vsₗ vsᵣ ⊢
    inf_array_model' t (vsₗ ++ [v]) vsᵣ'.
  Proof.
    intros. rewrite inf_array_model'_shift inf_array_model'_proper //.
  Qed.

  Lemma inf_array_create_spec default :
    {{{ True }}}
      inf_array_create default
    {{{ t,
      RET t;
      inf_array_inv t ∗
      inf_array_model t (λ _, default)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_apply (array_create_spec with "[//]"). iIntros "%data Hmodel_data".

    wp_smart_apply (record3_make_spec with "[//]"). iIntros "%l (Hl & Hmeta)".
    iDestruct (record3_model_eq_1 with "Hl") as "(Hdata & Hdefault & Hmtx)".
    iMod (mapsto_persist with "Hdefault") as "#Hdefault".

    set (vs _ := default).
    iMod (auth_excl_alloc' (auth_excl_G := inf_array_G_model_G) vs) as "(%γ & Hmodel₁ & Hmodel₂)".
    iMod (meta_set _ _ γ nroot with "Hmeta") as "#Hmeta"; first done.

    wp_smart_apply (mutex_create_spec _ (inf_array_inv_inner l γ default) with "[Hdata Hmodel_data Hmodel₂]"); iSteps.
  Qed.

  Lemma inf_array_get_spec t i :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vs,
      inf_array_model t vs
    >>>
      inf_array_get t #i
    <<<
      inf_array_model t vs
    | RET vs (Z.to_nat i); True
    >>>.
  Proof.
    iIntros "% !> %Φ (%l & %γ & %default & %mtx & -> & #Hmeta & #Hmtx & #Hdefault & #Hinv_mtx) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.

    wp_rec. wp_load.

    wp_apply (mutex_protect_spec _ Φ with "[$Hinv_mtx HΦ]"); last iSteps. iIntros "Hlocked_mtx (%data & %us & %vs & Hdata & Hmodel_data & Hmodel₂ & %Hvs)".

    wp_load.

    wp_smart_apply (array_size_spec with "Hmodel_data"). iIntros "Hmodel_data".

    wp_pures. case_decide.

    - rewrite bool_decide_eq_true_2; last lia.

      iApply wp_fupd.
      wp_smart_apply (array_unsafe_get_spec with "Hmodel_data"); [done | | done |].
      { rewrite Nat2Z.id list_lookup_lookup_total_lt //. lia. }

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      iSteps. rewrite decide_True; last lia. iSteps.

    - rewrite bool_decide_eq_false_2; last lia. wp_load.

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      iSteps. rewrite decide_False; last lia. iSteps.
  Qed.
  Lemma inf_array_get_spec' t i :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vsₗ vsᵣ,
      inf_array_model' t vsₗ vsᵣ
    >>>
      inf_array_get t #i
    <<<
      inf_array_model' t vsₗ vsᵣ
    | RET
        let i := Z.to_nat i in
        if decide (i < length vsₗ) then vsₗ !!! i else vsᵣ (i - length vsₗ);
      True
    >>>.
  Proof.
    iIntros "% !> %Φ Hinv HΦ".
    awp_apply (inf_array_get_spec with "Hinv"); first done.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vsₗ %vsᵣ Hmodel".
    iAaccIntro with "Hmodel"; iSteps.
  Qed.

  Lemma inf_array_set_spec t i v :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vs,
      inf_array_model t vs
    >>>
      inf_array_set t #i v
    <<<
      inf_array_model t (<[Z.to_nat i := v]> vs)
    | RET #(); True
    >>>.
  Proof.
    iIntros "% !> %Φ (%l & %γ & %default & %mtx & -> & #Hmeta & #Hmtx & #Hdefault & #Hinv_mtx) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.

    wp_rec. wp_load.

    wp_apply (mutex_protect_spec _ Φ with "[$Hinv_mtx HΦ]"); last iSteps. iIntros "Hlocked_mtx (%data & %us & %vs & Hdata & Hmodel_data & Hmodel₂ & %Hvs)".

    wp_load.

    wp_smart_apply (array_size_spec with "Hmodel_data"). iIntros "Hmodel_data".

    wp_pures. case_decide.

    - rewrite bool_decide_eq_true_2; last lia.

      iApply wp_fupd.
      wp_smart_apply (array_unsafe_set_spec with "Hmodel_data"); first done.

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
      set us' := <[i := v]> us.
      set vs' := <[i := v]> vs.
      iMod (auth_excl_update' (auth_excl_G := inf_array_G_model_G) vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      iIntros "Hmodel_data !>". iFrame. iSplitR "HΦ"; last iSteps.
      iExists data, us', vs'. rewrite Nat2Z.id. iFrame. iPureIntro.
      rewrite /us' /vs' insert_length Hvs.
      apply functional_extensionality => j. destruct (decide (j = i)) as [-> |].
      + rewrite fn_lookup_insert decide_True; last lia.
        rewrite list_lookup_total_insert //. lia.
      + rewrite fn_lookup_insert_ne //. case_decide; last done.
        rewrite list_lookup_total_insert_ne //.

    - rewrite bool_decide_eq_false_2; last lia. wp_load.

      wp_smart_apply (array_grow_spec with "Hmodel_data"); first lia. iIntros "%data' Hmodel_data'".
      rewrite Z.add_1_l -Nat2Z.inj_succ Nat2Z.id.

      wp_store.

      iApply wp_fupd.
      wp_apply (array_unsafe_set_spec with "Hmodel_data'").
      { rewrite app_length replicate_length. lia. }
      rewrite Nat2Z.id insert_app_r_alt; last lia.
      rewrite insert_replicate_lt; last lia.
      rewrite -Nat.sub_succ_l; last lia.
      rewrite Nat.sub_diag /=.
      iIntros "Hmodel_data'".

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
      set us' := us ++ replicate (i - length us) default ++ [v].
      set vs' := <[i := v]> vs.
      iMod (auth_excl_update' (auth_excl_G := inf_array_G_model_G) vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      iModIntro. iFrame. iSplitR "HΦ"; last iSteps.
      iExists data', us', vs'. iFrame. iPureIntro.
      rewrite /us' /vs' !app_length replicate_length Hvs /=.
      apply functional_extensionality => j. destruct (Nat.lt_total j i) as [| [-> |]].
      + rewrite fn_lookup_insert_ne; last lia.
        rewrite (@decide_True _ (j < _ + _)); last lia.
        case_decide.
        * rewrite lookup_total_app_l //.
        * rewrite lookup_total_app_r; last lia.
          rewrite lookup_total_app_l; last (rewrite replicate_length //; lia).
          rewrite lookup_total_replicate_2 //. lia.
      + rewrite fn_lookup_insert decide_True; last lia.
        rewrite lookup_total_app_r; last lia.
        rewrite lookup_total_app_r; last (rewrite replicate_length; lia).
        rewrite replicate_length Nat.sub_diag //.
      + rewrite fn_lookup_insert_ne; last lia.
        rewrite !decide_False //; lia.
  Qed.
  Lemma inf_array_set_spec' t i v :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vsₗ vsᵣ,
      inf_array_model' t vsₗ vsᵣ
    >>>
      inf_array_set t #i v
    <<<
      let i := Z.to_nat i in
      if decide (i < length vsₗ)
      then inf_array_model' t (<[i := v]> vsₗ) vsᵣ
      else inf_array_model' t vsₗ (<[i - length vsₗ := v]> vsᵣ)
    | RET #(); True
    >>>.
  Proof.
    iIntros "% !> %Φ Hinv HΦ".
    awp_apply (inf_array_set_spec with "Hinv"); first done.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vsₗ %vsᵣ Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    iSplitL "Hmodel"; last iSteps.
    Z_to_nat i. rewrite Nat2Z.id. case_decide.
    all: iApply (inf_array_model_proper with "Hmodel"); intros j.
    - rewrite insert_length. case_decide.
      + destruct (decide (j = i)) as [-> |].
        * rewrite list_lookup_total_insert // fn_lookup_insert //.
        * rewrite list_lookup_total_insert_ne // fn_lookup_insert_ne // decide_True //.
      + rewrite fn_lookup_insert_ne; last lia.
        rewrite decide_False //.
    - case_decide.
      + rewrite fn_lookup_insert_ne; last lia.
        rewrite decide_True //.
      + destruct (decide (j = i)) as [-> |].
        * rewrite !fn_lookup_insert //.
        * rewrite !fn_lookup_insert_ne; try lia.
           rewrite decide_False //.
  Qed.
End inf_array_G.

#[global] Opaque inf_array_create.
#[global] Opaque inf_array_get.
#[global] Opaque inf_array_set.

#[global] Opaque inf_array_inv.
#[global] Opaque inf_array_model.
#[global] Opaque inf_array_model'.
