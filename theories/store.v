From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  tactics
  notations.
From heap_lang.std Require Import
  record2
  record3.

Implicit Types r : loc.
Implicit Types v t s : val.
Implicit Types σ : gmap loc val.

#[local] Notation "t '.[root]'" :=
  t.[0]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[gen]'" :=
  t.[1]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[root]'" :=
  t.[#0]%E
( at level 5
) : expr_scope.
#[local] Notation "t '.[gen]'" :=
  t.[#1]%E
( at level 5
) : expr_scope.

#[local] Notation "r '.[ref_value]'" :=
  r.[0]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "r '.[ref_gen]'" :=
  r.[1]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "r '.[ref_value]'" :=
  r.[#0]%E
( at level 5
) : expr_scope.
#[local] Notation "r '.[ref_gen]'" :=
  r.[#1]%E
( at level 5
) : expr_scope.

#[local] Notation "s '.[snap_store]'" :=
  s.𝟙.𝟙%E
( at level 5
) : expr_scope.
#[local] Notation "s '.[snap_root]'" :=
  s.𝟙.𝟚%E
( at level 5
) : expr_scope.
#[local] Notation "s '.[snap_gen]'" :=
  s.𝟚%E
( at level 5
) : expr_scope.

#[local] Definition descr_match : val :=
  λ: "descr" "Root" "Diff",
    match: "descr" with
      InjL <> =>
        "Root" #()
    | InjR "x" =>
        "Diff" "x".𝟙.𝟙.𝟙 "x".𝟙.𝟙.𝟚 "x".𝟙.𝟚 "x".𝟚
    end.
#[local] Notation "'match:' e0 'with' | 'Root' => e1 | 'Diff' x1 x2 x3 x4 => e2 'end'" :=
  (descr_match e0 (λ: <>, e1) (λ: x1 x2 x3 x4, e2))%E
( x1, x2, x3, x4 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match:  e0  with  '/' '[' |  Root  =>  '/    ' e1 ']'  '/' '[' |  Diff  x1  x2  x3  x4  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
#[local] Notation "'match:' e0 'with' 'Root' => e1 | 'Diff' x1 x2 x3 x4 => e2 'end'" :=
  (descr_match e0 (λ: <>, e1) (λ: x1 x2 x3 x4, e2))%E
( x1, x2, x3, x4 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.
#[local] Notation "'match::' e0 'with' | 'Root' => e1 | 'Diff' x1 x2 x3 x4 => e2 'end'" :=
  (descr_match e0 (λ: <>, e1)%V (λ: x1 x2 x3 x4, e2)%V)%E
( x1, x2, x3, x4 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match::  e0  with  '/' '[' |  Root  =>  '/    ' e1 ']'  '/' '[' |  Diff  x1  x2  x3  x4  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
#[local] Notation "'match::' e0 'with' 'Root' => e1 | 'Diff' x1 x2 x3 x4 => e2 'end'" :=
  (descr_match e0 (λ: <>, e1)%V (λ: x1 x2 x3 x4, e2)%V)%E
( x1, x2, x3, x4 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.

#[local] Definition RootV :=
  InjLV #().
#[local] Notation "'&&Root'" :=
  RootV.
#[local] Instance pure_descr_match_Root e1 x1 x2 x3 x4 e2 :
  PureExec True 9
    (match:: &&Root with Root => e1 | Diff x1 x2 x3 x4 => e2 end)
    e1.
Proof.
  solve_pure_exec.
Qed.

#[local] Definition descr_Diff : val :=
  λ: "v1" "v2" "v3" "v4", InjR ("v1", "v2", "v3", "v4").
#[local] Definition DiffV v1 v2 v3 v4 :=
  InjRV (v1, v2, v3, v4).
#[local] Notation "'&Diff'" :=
  descr_Diff.
#[local] Notation "'&&Diff'" :=
  DiffV.
#[local] Lemma descr_Diff_inj v1 v2 v3 v4 w1 w2 w3 w4 :
  &&Diff v1 v2 v3 v4 = &&Diff w1 w2 w3 w4 →
  v1 = w1 ∧ v2 = w2 ∧ v3 = w3 ∧ v4 = w4.
Proof.
  naive_solver.
Qed.
#[local] Instance pure_descr_Diff v1 v2 v3 v4 :
  PureExec True 11
    (&Diff v1 v2 v3 v4)
    (&&Diff v1 v2 v3 v4).
Proof.
  solve_pure_exec.
Qed.
#[local] Instance pure_descr_match_Diff v1 v2 v3 v4 e1 x1 x2 x3 x4 e2 :
  PureExec True 24
    (match:: &&Diff v1 v2 v3 v4 with Root => e1 | Diff x1 x2 x3 x4 => e2 end)
    (subst' x1 v1 (subst' x2 v2 (subst' x3 v3 (subst' x4 v4 e2)))).
Proof.
  solve_pure_exec.
Qed.

#[global] Opaque descr_match.
#[global] Opaque RootV.
#[global] Opaque descr_Diff.
#[global] Opaque DiffV.

Definition store_create : val :=
  λ: <>,
    record2_make (ref &&Root) #0.

Definition store_ref : val :=
  λ: "t" "v",
    record2_make "v" #0.

Definition store_get : val :=
  λ: "t" "r",
    !"r".[ref_value].

Definition store_set : val :=
  λ: "t" "r" "v",
    if: !"t".[gen] = !"r".[ref_gen] then (
      "r".[ref_value] <- "v"
    ) else (
      let: "new_root" := ref &&Root in
      let: "old_root" := &Diff "r" !"r".[ref_value] !"r".[ref_gen] "new_root" in
      "r".[ref_value] <- "v" ;;
      "r".[ref_gen] <- !"t".[gen] ;;
      !"t".[root] <- "old_root" ;;
      "t".[root] <- "new_root"
    ).

Definition store_capture : val :=
  λ: "t",
    let: "g" := !"t".[gen] in
    "t".[gen] <- #1 + "g" ;;
    ("t", !"t".[root], "g").

#[local] Definition store_reroot : val :=
  rec: "store_reroot" "node" :=
    match: !"node" with
    | Root =>
        #()
    | Diff "r" "v" "g" "node'" =>
        "store_reroot" "node'" ;;
        "node'" <- &Diff "r" !"r".[ref_value] !"r".[gen] "node" ;;
        "r".[ref_value] <- "v" ;;
        "r".[ref_gen] <- "g" ;;
        "node" <- &&Root
    end.

#[local] Definition store_reroot_opt_aux : val :=
  rec: "store_reroot_opt_aux" "node" :=
    match: !"node" with
    | Root =>
        #()
    | Diff "r" "v" "g" "node'" =>
        "store_reroot_opt_aux" "node'" ;;
        "node'" <- &Diff "r" !"r".[ref_value] !"r".[ref_gen] "node" ;;
        "r".[ref_value] <- "v" ;;
        "r".[ref_gen] <- "g"
    end.
#[local] Definition store_reroot_opt : val :=
  λ: "node",
    match: !"node" with
    | Root =>
        #()
    | Diff <> <> <> <> =>
        store_reroot_opt_aux "node" ;;
        "node" <- &&Root
    end.

Definition store_restore : val :=
  λ: "t" "s",
    if: "t" ≠ !"s".[snap_store] then (
      Fail
    ) else (
      let: "root" := !"s".[snap_root] in
      if: !"root" = &&Root then (
        #()
      ) else (
        store_reroot "root" ;;
        "t".[root] <- "root" ;;
        "t".[gen] <- #1 + !"s".[snap_gen]
      )
    ).

Class StoreG Σ `{heap_GS : !heapGS Σ} := {
}.

Definition store_Σ := #[
].
Lemma subG_store_Σ Σ `{heap_GS : !heapGS Σ} :
  subG store_Σ Σ →
  StoreG Σ.
Proof.
  solve_inG.
Qed.

Section store_G.
  Context `{store_G : StoreG Σ}.

  Definition store_store σ0 σ :=
    union_with (λ _, Some) σ0 σ.

  Definition store_model t σ0 σ : iProp Σ.
  Proof. Admitted.

  Definition store_snapshot_model s t σ : iProp Σ.
  Proof. Admitted.

  #[global] Instance store_model_timeless t σ0 σ :
    Timeless (store_model t σ0 σ).
  Proof.
  Abort.
  #[global] Instance store_snapshot_persistent s t σ :
    Persistent (store_snapshot_model s t σ).
  Proof.
  Abort.

  Lemma store_create_spec :
    {{{ True }}}
      store_create #()
    {{{ t,
      RET t;
      store_model t ∅ ∅
    }}}.
  Proof.
  Abort.

  Lemma store_ref_spec t σ0 σ v :
    {{{
      store_model t σ0 σ
    }}}
      store_ref t v
    {{{ r,
      RET #r;
      store_model t (<[r := v]> σ0) σ
    }}}.
  Proof.
  Abort.

  Lemma store_get_spec {t σ0 σ r} v :
    store_store σ0 σ !! r = Some v →
    {{{
      store_model t σ0 σ
    }}}
      store_get t #r
    {{{
      RET v;
      store_model t σ0 σ
    }}}.
  Proof.
  Abort.

  Lemma store_set_spec t σ0 σ r v :
    r ∈ dom σ0 →
    {{{
      store_model t σ0 σ
    }}}
      store_set t #r v
    {{{
      RET #();
      store_model t σ0 (<[r := v]> σ)
    }}}.
  Proof.
  Abort.

  Lemma store_catpure_spec t σ0 σ :
    {{{
      store_model t σ0 σ
    }}}
      store_capture t
    {{{ s,
      RET s;
      store_model t σ0 σ ∗
      store_snapshot_model s t σ
    }}}.
  Proof.
  Abort.

  Lemma store_restore_spec t σ0 σ s σ' :
    {{{
      store_model t σ0 σ ∗
      store_snapshot_model s t σ'
    }}}
      store_restore t s
    {{{
      RET #();
      store_model t σ0 σ'
    }}}.
  Proof.
  Abort.
End store_G.

#[global] Opaque store_create.
#[global] Opaque store_ref.
#[global] Opaque store_get.
#[global] Opaque store_set.
#[global] Opaque store_capture.
#[global] Opaque store_restore.

#[global] Opaque store_model.
#[global] Opaque store_snapshot_model.
