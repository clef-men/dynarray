From iris.base_logic Require Import
  lib.ghost_map.

From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  tactics
  notations
  proofmode.
From heap_lang.std Require Import
  array.
From heap_lang.persistent Require Export
  base.

Implicit Types i : nat.
Implicit Types l root : loc.
Implicit Types v t eq : val.
Implicit Types vs : list val.

#[local] Definition descr_match : val :=
  λ: "descr" "Root" "Diff",
    match: "descr" with
      InjL "x" =>
        "Root" "x"
    | InjR "y" =>
        "Diff" "y".1.1 "y".1.2 "y".2
    end.
#[local] Notation "'match:' e0 'with' | 'Root' x => e1 | 'Diff' y1 y2 y3 => e2 'end'" :=
  (descr_match e0 (λ: x, e1) (λ: y1 y2 y3, e2))%E
( x, y1, y2, y3 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match:  e0  with  '/' '[' |  Root  x  =>  '/    ' e1 ']'  '/' '[' |  Diff  y1  y2  y3  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
#[local] Notation "'match:' e0 'with' 'Root' x => e1 | 'Diff' y1 y2 y3 => e2 'end'" :=
  (descr_match e0 (λ: x, e1) (λ: y1 y2 y3, e2))%E
( x, y1, y2, y3 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.
#[local] Notation "'match::' e0 'with' | 'Root' x => e1 | 'Diff' y1 y2 y3 => e2 'end'" :=
  (descr_match e0 (λ: x, e1)%V (λ: y1 y2 y3, e2)%V)%E
( x, y1, y2, y3 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match::  e0  with  '/' '[' |  Root  x  =>  '/    ' e1 ']'  '/' '[' |  Diff  y1  y2  y3  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
#[local] Notation "'match::' e0 'with' 'Root' x => e1 | 'Diff' y1 y2 y3 => e2 'end'" :=
  (descr_match e0 (λ: x, e1)%V (λ: y1 y2 y3, e2)%V)%E
( x, y1, y2, y3 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.

#[local] Definition descr_Root : val :=
  λ: "v", InjL "v".
#[local] Definition RootV :=
  InjLV.
#[local] Notation "'&Root'" :=
  descr_Root.
#[local] Notation "'&&Root'" :=
  RootV.
#[local] Instance pure_descr_Root v :
  PureExec True 2
    (&Root v)
    (&&Root v).
Proof.
  solve_pure_exec.
Qed.
#[local] Instance pure_descr_match_Root v x e1 y1 y2 y3 e2 :
  PureExec True 9
    (match:: &&Root v with Root x => e1 | Diff y1 y2 y3 => e2 end)
    (subst' x v e1).
Proof.
  solve_pure_exec.
Qed.

#[local] Definition descr_Diff : val :=
  λ: "v1" "v2" "v3", InjR ("v1", "v2", "v3").
#[local] Definition DiffV v1 v2 v3 :=
  InjRV (v1, v2, v3).
#[local] Notation "'&Diff'" :=
  descr_Diff.
#[local] Notation "'&&Diff'" :=
  DiffV.
#[local] Instance pure_descr_Diff v1 v2 v3 :
  PureExec True 8
    (&Diff v1 v2 v3)
    (&&Diff v1 v2 v3).
Proof.
  solve_pure_exec.
Qed.
#[local] Instance pure_descr_match_Diff v1 v2 v3 x e1 y1 y2 y3 e2 :
  PureExec True 18
    (match:: &&Diff v1 v2 v3 with Root x => e1 | Diff y1 y2 y3 => e2 end)
    (subst' y1 v1 (subst' y2 v2 (subst' y3 v3 e2))).
Proof.
  solve_pure_exec.
Qed.

#[global] Opaque descr_match.
#[global] Opaque descr_Root.
#[global] Opaque RootV.
#[global] Opaque descr_Diff.
#[global] Opaque DiffV.

Definition parray_make : val :=
  λ: "sz" "v",
    ref (&Root (array_make "sz" "v")).

#[local] Definition parray_reroot : val :=
  rec: "parray_reroot" "t" :=
    match: !"t" with
    | Root "arr" =>
        "arr"
    | Diff "i" "v" "t'" =>
        let: "arr" := "parray_reroot" "t'" in
        let: "v'" := array_unsafe_get "arr" "i" in
        array_unsafe_set "arr" "i" "v" ;;
        "t'" <- &Diff "i" "v'" "t" ;;
        "t" <- &Root "arr" ;;
        "arr"
    end.

Definition parray_get : val :=
  λ: "t" "i",
    array_unsafe_get (parray_reroot "t") "i".

Definition parray_set : val :=
  λ: "t" "eq" "i" "v",
    let: "arr" := parray_reroot "t" in
    let: "v'" := array_unsafe_get "arr" "i" in
    if: "eq" "v" "v'" then (
      "t"
    ) else (
      array_unsafe_set "arr" "i" "v" ;;
      let: "t'" := ref !"t" in
      "t" <- &Diff "i" "v'" "t'" ;;
      "t'"
    ).

Class ParrayG Σ `{heap_GS : !heapGS Σ} := {
  parray_G_map_G : ghost_mapG Σ loc (list val) ;
}.

Section parray_G.
  Context `{parray_G : ParrayG Σ}.

  Record parray_name := {
    parray_name_map : gname ;
    parray_name_array : val ;
    parray_name_size : nat ;
  }.
  Implicit Types γ : parray_name.

  #[local] Definition parray_map_auth' γ_map map :=
    @ghost_map_auth _ _ _ _ _ parray_G_map_G γ_map 1 map.
  #[local] Definition parray_map_auth γ :=
    parray_map_auth' γ.(parray_name_map).
  #[local] Definition parray_map_elem' γ_map l vs :=
    @ghost_map_elem _ _ _ _ _ parray_G_map_G γ_map l DfracDiscarded vs.
  #[local] Definition parray_map_elem γ :=
    parray_map_elem' γ.(parray_name_map).

  #[local] Definition parray_inv_inner τ `{!iType _ τ} γ map root : iProp Σ :=
    parray_map_auth γ map ∗
    [∗ map] l ↦ vs ∈ map,
      ∃ descr,
      ⌜length vs = γ.(parray_name_size)⌝ ∗
      l ↦ descr ∗
      if (decide (l = root)) then (
        ⌜descr = &&Root γ.(parray_name_array)⌝ ∗
        array_model γ.(parray_name_array) (DfracOwn 1) vs ∗
        [∗ list] v ∈ vs, τ v
      ) else (
        ∃ i v l' vs',
        ⌜i < γ.(parray_name_size) ∧ vs = <[i := v]> vs'⌝ ∗
        ⌜descr = &&Diff #i v #l'⌝ ∗
        parray_map_elem γ l' vs' ∗
        τ v
      ).
  Definition parray_inv τ `{!iType _ τ} γ : iProp Σ :=
    ∃ map root,
    parray_inv_inner τ γ map root.

  Definition parray_model t γ vs : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    parray_map_elem γ l vs.

  #[local] Instance parray_inv_inner_timeless τ `{!iType _ τ} γ map root :
    (∀ v, Timeless (τ v)) →
    Timeless (parray_inv_inner τ γ map root).
  Proof.
    rewrite /Timeless. iIntros (Hτ) "(Hmap_auth & Hmap)".
    iSplitL "Hmap_auth".
    - iApply (timeless with "Hmap_auth").
    - unshelve iApply (timeless _ (Timeless := big_sepM_timeless _ _ _) with "Hmap").
      rewrite /Timeless. iIntros (l vs Hlookup) "(%descr & >%Hvs_len & Hl & Hdescr)".
      iExists descr.
      iSplit; first iSmash.
      iSplitL "Hl"; first iApply (timeless with "Hl").
      case_decide as Hcase.
      + iDestruct "Hdescr" as "(>-> & Harr & Hvs)".
        iSplit; first iSmash.
        iSplitL "Harr"; first iApply (timeless with "Harr").
        unshelve iApply (timeless _ (Timeless := big_sepL_timeless _ _ _) with "Hvs").
        rewrite /Timeless. iSteps. iApply Hτ. iSmash.
      + iDestruct "Hdescr" as "(%i & %v & %l' & %vs' & >(%Hi & %Hvs) & >-> & Hmap_elem' & Hτ)".
        iExists i, v, l', vs'.
        iSplit; first iSmash.
        iSplit; first iSmash.
        iSplit; first iApply (timeless with "Hmap_elem'").
        iApply (Hτ with "Hτ").
  Qed.
  #[global] Instance parray_inv_timeless τ `{!iType _ τ} γ :
    (∀ v, Timeless (τ v)) →
    Timeless (parray_inv τ γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance parray_model_timeless t γ vs :
    Timeless (parray_model t γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance parray_model_persistent t γ vs :
    Persistent (parray_model t γ vs).
  Proof.
    apply _.
  Qed.

  #[local] Lemma parray_map_alloc root vs :
    ⊢ |==>
      ∃ γ_map,
      parray_map_auth' γ_map {[root := vs]} ∗
      parray_map_elem' γ_map root vs.
  Proof.
    iMod (@ghost_map_alloc _ _ _ _ _ parray_G_map_G {[root := vs]}) as "(%γ_map & Hmap_auth & Hmap_elem)".
    setoid_rewrite big_sepM_singleton.
    iMod (ghost_map_elem_persist with "Hmap_elem") as "Hmap_elem".
    iSmash.
  Qed.
  #[local] Lemma parray_map_lookup γ map l vs :
    parray_map_auth γ map -∗
    parray_map_elem γ l vs -∗
    ⌜map !! l = Some vs⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma parray_map_insert {γ map} l vs :
    map !! l = None →
    parray_map_auth γ map ⊢ |==>
      parray_map_auth γ (<[l := vs]> map) ∗
      parray_map_elem γ l vs.
  Proof.
    iIntros "%Hlookup Hmap_auth".
    iMod (ghost_map_insert with "Hmap_auth") as "(Hmap_auth & Hmap_elem)"; first done.
    iMod (ghost_map_elem_persist with "Hmap_elem") as "Hmap_elem".
    iSmash.
  Qed.

  Lemma parray_make_spec τ `{!iType _ τ} (sz : Z) v :
    (0 ≤ sz)%Z →
    {{{
      τ v
    }}}
      parray_make #sz v
    {{{ t γ,
      RET t;
      parray_inv τ γ ∗
      parray_model t γ (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply (array_make_spec with "[//]"); first done. iIntros "%arr Harr".
    wp_alloc root as "Hroot".
    pose vs := replicate (Z.to_nat sz) v.
    iMod (parray_map_alloc root vs) as "(%γ_map & Hmap_auth & Hmap_elem)".
    pose γ := {|
      parray_name_map := γ_map ;
      parray_name_array := arr ;
      parray_name_size := Z.to_nat sz ;
    |}.
    iApply ("HΦ" $! _ γ). iSplitR "Hmap_elem"; last iSmash. iExists {[root := vs]}, root. iFrame.
    iApply big_sepM_singleton.
    iExists _. rewrite replicate_length decide_True //. iSteps.
    iApply big_sepL_intro. iIntros "!> !>" (i ? (-> & Hi)%lookup_replicate) "//".
  Qed.

  #[local] Lemma parray_reroot_spec τ `{!iType _ τ} γ map root l vs :
    {{{
      parray_inv_inner τ γ map root ∗
      parray_map_elem γ l vs
    }}}
      parray_reroot #l
    {{{
      RET γ.(parray_name_array);
      parray_inv_inner τ γ map l
    }}}.
  Proof.
    iLöb as "HLöb" forall (l vs).
    iIntros "%Φ ((Hmap_auth & Hmap) & #Hmap_elem) HΦ".
    wp_rec.
    iDestruct (parray_map_lookup with "Hmap_auth Hmap_elem") as %Hmap_lookup.
    iDestruct (big_sepM_lookup_acc with "Hmap") as "((%descr & %Hvs_len & Hl & Hdescr) & Hmap)"; first done.
    destruct (decide (l = root)) as [-> | Hcase1].
    { iDestruct "Hdescr" as "(-> & Harr & Hvs)". iSmash. }
    iDestruct "Hdescr" as "(%i & %v & %l' & %vs' & (%Hi & %Hvs) & -> & #Hmap_elem' & #Hv)".
    wp_load.
    iDestruct ("Hmap" with "[Hl Hv]") as "Hmap"; first iSmash.
    wp_smart_apply ("HLöb" with "[Hmap_auth Hmap]"); first iSmash. iIntros "(Hmap_auth & Hmap)".
    wp_pures.
    iDestruct (parray_map_lookup with "Hmap_auth Hmap_elem'") as %Hmap_lookup'.
    iDestruct (big_sepM_delete with "Hmap") as "((%descr' & %Hvs'_len & Hl' & Hdescr') & Hmap)"; first done.
    rewrite decide_True //. iDestruct "Hdescr'" as "(-> & Harr & Hvs')".
    feed pose proof (list_lookup_lookup_total_lt vs' i) as Hvs'_lookup; first lia.
    wp_smart_apply (array_unsafe_get_spec i with "Harr"); [lia | | lia |]; first done. iIntros "Harr".
    wp_smart_apply (array_unsafe_set_spec with "Harr"); first lia. iIntros "Harr".
    rewrite Nat2Z.id -Hvs.
    wp_store.
    destruct (decide (l = l')) as [<- | Hcase2].
    - wp_store.
      iDestruct (big_sepM_delete with "[$Hmap Hl' Harr Hvs']") as "Hmap"; first done.
      { iExists _. rewrite decide_True //. clear Hvs. iSmash. }
      iSmash.
    - iDestruct (big_sepM_delete _ _ l with "Hmap") as "((%descr & _ & Hl & Hdescr) & Hmap)".
      { rewrite lookup_delete_ne //. }
      rewrite decide_False //. iDestruct "Hdescr" as "(%i' & %v' & %l'' & %vs'' & _ & -> & _ & _)".
      wp_store.
      iApply "HΦ". iFrame.
      iDestruct (big_sepL_insert_acc with "Hvs'") as "(Hvs'!!!i & Hvs')"; first done.
      iApply (big_sepM_delete _ _ l'); first done. iSplitL "Hl' Hvs'!!!i".
      { iExists _. rewrite decide_False //. iFrame. iSplitR; first iSmash. iExists i, (vs' !!! i), l, vs. iSteps.
        iPureIntro. rewrite list_insert_insert list_insert_id //.
      }
      iApply (big_sepM_delete _ _ l); first rewrite lookup_delete_ne //. iSplitL "Hl Harr Hvs'".
      { iExists _. rewrite decide_True //. iSmash. }
      iApply (big_sepM_impl with "Hmap"). clear. iIntros "!> !>" (l'' vs'' (Hl''1 & (Hl''2 & Hmap_lookup'')%lookup_delete_Some)%lookup_delete_Some) "(%descr'' & %Hvs''_len & Hl'' & Hdescr'')".
      iExists _. rewrite decide_False // decide_False //. iFrame. iSmash.
  Qed.

  Lemma parray_get_spec τ `{!iType _ τ} {t γ vs} {i : Z} v :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      parray_inv τ γ ∗
      parray_model t γ vs
    }}}
      parray_get t #i
    {{{
      RET v;
      parray_inv τ γ
    }}}.
  Proof.
    iIntros "%Hi %Hvs_lookup %Φ ((%map & %root & Hinv) & (%l & -> & #Hmap_elem)) HΦ".
    wp_rec.
    wp_smart_apply (parray_reroot_spec τ with "[$Hinv $Hmap_elem]"). iIntros "(Hmap_auth & Hmap)".
    iDestruct (parray_map_lookup with "Hmap_auth Hmap_elem") as %Hmap_lookup.
    iDestruct (big_sepM_lookup_acc with "Hmap") as "((%descr & %Hvs_len & Hl & Hdescr) & Hmap)"; first done.
    rewrite decide_True //. iDestruct "Hdescr" as "(-> & Harr & Hvs)".
    wp_apply (array_unsafe_get_spec with "Harr"); [done.. |].
    setoid_rewrite decide_True at 1; last done. iSteps. iExists l. iSmash.
  Qed.

  Lemma parray_set_spec τ `{!iType _ τ} t γ vs eq (i : Z) v :
    (0 ≤ i < length vs)%Z →
    {{{
      parray_inv τ γ ∗
      parray_model t γ vs ∗
      ( ∀ v1 v2,
        τ v1 -∗
        τ v2 -∗
        WP eq v1 v2 {{ res,
          ⌜res = #(bool_decide (v1 = v2))⌝
        }}
      ) ∗
      τ v
    }}}
      parray_set t eq #i v
    {{{ t',
      RET t';
      parray_inv τ γ ∗
      parray_model t' γ (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ ((%map & %root & Hinv) & (%l & -> & #Hmap_elem) & Heq & #Hv) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    wp_rec.
    wp_smart_apply (parray_reroot_spec with "[$Hinv //]"). iIntros "(Hmap_auth & Hmap)".
    iDestruct (parray_map_lookup with "Hmap_auth Hmap_elem") as %Hmap_lookup.
    iDestruct (big_sepM_delete _ _ l with "Hmap") as "((%descr & %Hvs_len & Hl & Hdescr) & Hmap)"; first done.
    rewrite decide_True //. iDestruct "Hdescr" as "(-> & Harr & Hvs)".
    feed pose proof (list_lookup_lookup_total_lt vs i); first lia.
    wp_smart_apply (array_unsafe_get_spec i with "Harr"); [lia | done | lia |]. iIntros "Harr".
    iDestruct (big_sepL_insert_acc with "Hvs") as "(#Hvs!!!i & Hvs)"; first done.
    wp_smart_apply (wp_wand with "(Heq Hv Hvs!!!i)"). iIntros "% ->".
    wp_pures. case_bool_decide as Hcase; wp_pures.
    - iDestruct ("Hvs" with "Hv") as "Hvs".
      rewrite list_insert_id; first congruence.
      iDestruct (big_sepM_delete with "[Hl Harr Hvs $Hmap]") as "Hmap"; first done.
      { iExists _. rewrite decide_True //. iSmash. }
      iSmash.
    - wp_apply (array_unsafe_set_spec with "Harr"); first done. iIntros "Harr". rewrite Nat2Z.id.
      wp_load. clear root. wp_alloc root as "Hroot". wp_store.
      iApply "HΦ".
      iAssert ⌜map !! root = None⌝%I as %Hmap_lookup_root.
      { rewrite -eq_None_ne_Some. iIntros "%vs_root %Hmap_lookup_root".
        iDestruct (mapsto_ne with "Hroot Hl") as %Hne.
        iDestruct (big_sepM_lookup _ _ root with "Hmap") as "(%descr & _ & Hroot_ & _)"; first rewrite lookup_delete_ne //.
        iDestruct (mapsto_ne with "Hroot Hroot_") as %[]. done.
      }
      set vs_root := <[i := v]> vs.
      iMod (parray_map_insert root vs_root with "Hmap_auth") as "(Hmap_auth & #Hmap_elem_root)"; first done.
      iSplitR "Hmap_elem_root"; last iSmash. iExists (<[root := vs_root]> map), root. iFrame.
      iApply (big_sepM_insert _ _ root); first done. iSplitL "Hroot Harr Hvs".
      { iExists _. rewrite decide_True //. iSteps. rewrite insert_length //. }
      iApply (big_sepM_delete _ _ l); first done. iSplitL "Hl".
      { iExists _. rewrite decide_False; first congruence. iStep 2. iExists i, (vs !!! i), root, vs_root. iSteps.
        iPureIntro. rewrite /vs_root list_insert_insert list_insert_id //.
      }
      iApply (big_sepM_impl with "Hmap"). iIntros "!> !>" (l' vs'' (Hne & Hmap_lookup')%lookup_delete_Some) "(%descr' & %Hvs'_len & Hl' & Hdescr')".
      iExists _. rewrite decide_False // decide_False; first congruence. iFrame. iSmash.
  Qed.
End parray_G.

#[global] Opaque parray_make.
#[global] Opaque parray_get.
#[global] Opaque parray_set.

#[global] Opaque parray_inv.
#[global] Opaque parray_model.
