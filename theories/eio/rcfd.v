From heap_lang Require Import
  prelude.
From heap_lang.common Require Import
  gmultiset.
From heap_lang.iris.base_logic Require Import
  lib.auth_gmultiset
  lib.mono_state.
From heap_lang.language Require Import
  tactics
  notations
  diaframe.
From heap_lang.std Require Import
  record2
  opt
  channel1
  unix.
From heap_lang.eio Require Import
  base.

Implicit Types b closing : bool.
Implicit Types ops : Z.
Implicit Types q : Qp.
Implicit Types qs : gmultiset Qp.
Implicit Types l l_state : loc.
Implicit Types t v v_state fd fn : val.
Implicit Types o : option val.

#[local] Definition state_match : val :=
  λ: "state" "Open" "Closing",
    match: "state" with
      InjL "x1" =>
        "Open" "x1"
    | InjR "x2" =>
        "Closing" "x2"
    end.
#[local] Notation "'match:' e0 'with' | 'Open' x1 => e1 | 'Closing' x2 => e2 'end'" :=
  (state_match e0 (λ: x1, e1) (λ: x2, e2))%E
( x1, x2 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match:  e0  with  '/' '[' |  Open  x1  =>  '/    ' e1 ']'  '/' '[' |  Closing  x2  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
#[local] Notation "'match:' e0 'with' 'Open' x1 => e1 | 'Closing' x2 => e2 'end'" :=
  (state_match e0 (λ: x1, e1) (λ: x2, e2))%E
( x1, x2 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.
#[local] Notation "'match::' e0 'with' | 'Open' x1 => e1 | 'Closing' x2 => e2 'end'" :=
  (state_match e0 (λ: x1, e1)%V (λ: x2, e2)%V)%E
( x1, x2 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match::  e0  with  '/' '[' |  Open  x1  =>  '/    ' e1 ']'  '/' '[' |  Closing  x2  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
#[local] Notation "'match::' e0 'with' 'Open' x1 => e1 | 'Closing' x2 => e2 'end'" :=
  (state_match e0 (λ: x1, e1)%V (λ: x2, e2)%V)%E
( x1, x2 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.

#[local] Definition state_Open : val :=
  λ: "v", InjL "v".
#[local] Definition OpenV :=
  InjLV.
#[local] Notation "'&Open'" :=
  state_Open.
#[local] Notation "'&&Open'" :=
  OpenV.
#[local] Instance state_Open_inj :
  Inj (=) (=) &&Open.
Proof.
  rewrite /Inj. naive_solver.
Qed.
#[local] Instance pure_state_Open v :
  PureExec True 2
    (&Open v)
    (&&Open v).
Proof.
  solve_pure_exec.
Qed.
#[local] Instance pure_state_match_Open v x1 e1 x2 e2 :
  PureExec True 9
    (match:: &&Open v with Open x1 => e1 | Closing x2 => e2 end)
    (subst' x1 v e1).
Proof.
  solve_pure_exec.
Qed.

#[local] Definition state_Closing : val :=
  λ: "v", InjR "v".
#[local] Definition ClosingV :=
  InjRV.
#[local] Notation "'&Closing'" :=
  state_Closing.
#[local] Notation "'&&Closing'" :=
  ClosingV.
#[local] Instance state_Closing_inj :
  Inj (=) (=) &&Closing.
Proof.
  rewrite /Inj. naive_solver.
Qed.
#[local] Instance pure_state_Closing v :
  PureExec True 2
    (&Closing v)
    (&&Closing v).
Proof.
  solve_pure_exec.
Qed.
#[local] Instance pure_state_match_Closing v x1 e1 x2 e2 :
  PureExec True 9
    (match:: &&Closing v with Open x1 => e1 | Closing x2 => e2 end)
    (subst' x2 v e2).
Proof.
  solve_pure_exec.
Qed.

#[global] Opaque state_match.
#[global] Opaque OpenV.
#[global] Opaque state_Closing.
#[global] Opaque ClosingV.

Inductive rcfd_state :=
  | RcfdStateOpen fd
  | RcfdStateClosing fn.
Implicit Types state : rcfd_state.

#[local] Instance rcfd_state_inhabited : Inhabited rcfd_state :=
  populate (RcfdStateOpen inhabitant).
#[local] Instance rcfd_state_eq_dec : EqDecision rcfd_state :=
  ltac:(solve_decision).

#[local] Definition state_to_val state :=
  match state with
  | RcfdStateOpen fd =>
      &&Open fd
  | RcfdStateClosing fn =>
      &&Closing fn
  end.
#[local] Arguments state_to_val !_ / : assert.
#[local] Coercion state_to_val : rcfd_state >-> val.

#[local] Instance state_to_val_inj :
  Inj (=) (=) state_to_val.
Proof.
  intros [] []; naive_solver.
Qed.

#[local] Notation "t '.[ops]'" :=
  t.[0]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[fd]'" :=
  t.[1]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[ops]'" :=
  t.[#0]%E
( at level 5
) : expr_scope.
#[local] Notation "t '.[fd]'" :=
  t.[#1]%E
( at level 5
) : expr_scope.

Definition rcfd_make : val :=
  λ: "fd",
    record2_make #0 (ref (&Open "fd")).

#[local] Definition rcfd_closed : val :=
  λ: <>,
    ref (&Closing (λ: <>, #())).

#[local] Definition rcfd_put : val :=
  λ: "t",
    let: "old" := FAA "t".[ops] #-1 in
    if: "old" = #1 then (
      let: "prev" := !"t".[fd] in
      match: !"prev" with
      | Open <> =>
          #()
      | Closing "no_users" =>
          if: #0 < !"t".[ops] then (
            #()
          ) else if: CAS "t".[fd] "prev" (rcfd_closed #()) then (
            "no_users" #()
          ) else (
            #()
          )
      end
    ) else (
      #()
    ).

#[local] Definition rcfd_get : val :=
  λ: "t",
    FAA "t".[ops] #1 ;;
    match: ! !"t".[fd] with
    | Open "fd" =>
        &Some "fd"
    | Closing <> =>
        rcfd_put "t" ;;
        &&None
    end.

Definition rcfd_close : val :=
  λ: "t",
    let: "prev" := !"t".[fd] in
    match: !"prev" with
    | Open "fd" =>
        let: "close" := λ: <>, unix_close "fd" in
        let: "next" := ref (&Closing "close") in
        if: CAS "t".[fd] "prev" "next" then (
          (if: (!"t".[ops] = #0) && CAS "t".[fd] "next" (rcfd_closed #()) then (
            "close" #()
          ) else (
            #()
          )) ;;
          #true
        ) else (
          #false
        )
    | Closing <> =>
        #false
    end.

Definition rcfd_remove `{heap_GS : !heapGS Σ} {mutex : mutex Σ} (condition : condition mutex) : val :=
  λ: "t",
    let: "prev" := !"t".[fd] in
    match: !"prev" with
    | Open "fd" =>
        let: "flag" := ref #false in
        let: "chan" := channel1_create condition #() in
        let: "next" := ref (&Closing (λ: <>, channel1_signal condition "chan")) in
        if: CAS "t".[fd] "prev" "next" then (
          channel1_wait condition "chan" ;;
          &Some "fd"
        ) else (
          &&None
        )
    | Closing <> =>
        &&None
    end.

Definition rcfd_use : val :=
  λ: "t" "closed" "open",
    match: rcfd_get "t" with
    | None =>
        "closed" #()
    | Some "fd" =>
        let: "res" := "open" "fd" in
        rcfd_put "t" ;;
        "res"
    end.

Definition rcfd_is_open : val :=
  λ: "t",
    match: ! !"t".[fd] with
    | Open <> =>
        #true
    | Closing <> =>
        #false
    end.

Definition rcfd_peek : val :=
  λ: "t",
    match: ! !"t".[fd] with
    | Open "fd" =>
        &Some "fd"
    | Closing <> =>
        &&None
    end.

Inductive rcfd_lstate :=
  | RcfdLstateOpen
  | RcfdLstateClosingUsers
  | RcfdLstateClosingNoUsers.
Implicit Types lstate : rcfd_lstate.

#[global] Instance rcfd_lstate_inhabited : Inhabited rcfd_lstate :=
  populate RcfdLstateOpen.
#[global] Instance rcfd_lstate_eq_dec : EqDecision rcfd_lstate :=
  ltac:(solve_decision).

Inductive rcfd_lstep : relation rcfd_lstate :=
  | rcfd_step_close_users :
      rcfd_lstep RcfdLstateOpen RcfdLstateClosingUsers
  | rcfd_step_close_no_users :
      rcfd_lstep RcfdLstateClosingUsers RcfdLstateClosingNoUsers.
#[local] Hint Constructors rcfd_lstep : core.

Class RcfdG Σ `{heap_GS : !heapGS Σ} := {
  #[local] rcfd_G_tokens_G :: AuthGmultisetG Σ Qp ;
  #[local] rcfd_G_lstate_G :: MonoStateG rcfd_lstep Σ ;
  #[local] rcfd_G_channel1_G :: Channel1G Σ ;
}.

Definition rcfd_Σ := #[
  auth_gmultiset_Σ Qp ;
  mono_state_Σ rcfd_lstep ;
  channel1_Σ
].
#[global] Instance subG_rcfd_Σ `{heap_GS : !heapGS Σ} :
  subG rcfd_Σ Σ →
  RcfdG Σ.
Proof.
  solve_inG.
Qed.

Section rcfd_G.
  Context `{rcfd_G : RcfdG Σ}.

  Record rcfd_meta := {
    rcfd_meta_tokens : gname ;
    rcfd_meta_lstate : gname ;
    rcfd_meta_open_state : loc ;
  }.
  Implicit Types γ : rcfd_meta.

  #[global] Instance rcfd_meta_eq_dec : EqDecision rcfd_meta :=
    ltac:(solve_decision).
  #[global] Instance rcfd_meta_countable :
    Countable rcfd_meta.
  Proof.
    pose encode γ := (
      γ.(rcfd_meta_tokens),
      γ.(rcfd_meta_lstate),
      γ.(rcfd_meta_open_state)
    ).
    pose decode := λ '(γ_tokens, γ_lstate, γ_open_state), {|
      rcfd_meta_tokens := γ_tokens ;
      rcfd_meta_lstate := γ_lstate ;
      rcfd_meta_open_state := γ_open_state ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition rcfd_tokens_auth' γ_tokens qs :=
    auth_gmultiset_auth γ_tokens (DfracOwn 1) qs.
  #[local] Definition rcfd_tokens_auth γ qs :=
    rcfd_tokens_auth' γ.(rcfd_meta_tokens) qs.
  #[local] Definition rcfd_tokens_frag γ q :=
    auth_gmultiset_frag γ.(rcfd_meta_tokens) {[+q+]}.

  #[local] Definition rcfd_lstate_auth' γ_lstate lstate :=
    mono_state_auth rcfd_lstep γ_lstate (DfracOwn 1) lstate.
  #[local] Definition rcfd_lstate_auth γ lstate :=
    rcfd_lstate_auth' γ.(rcfd_meta_lstate) lstate.
  #[local] Definition rcfd_lstate_lb γ lstate :=
    mono_state_lb rcfd_lstep γ.(rcfd_meta_lstate) lstate.

  #[local] Definition rcfd_inv_inner l γ fd chars : iProp Σ :=
    ∃ state lstate ops l_state,
    l.[ops] ↦ #ops ∗
    l.[fd] ↦ #l_state ∗ l_state ↦□ (state : val) ∗
    rcfd_lstate_auth γ lstate ∗
    match lstate with
    | RcfdLstateOpen =>
        ∃ q qs,
        ⌜ops = size qs ∧ set_fold Qp.add q qs = 1%Qp⌝ ∗
        ⌜l_state = γ.(rcfd_meta_open_state) ∧ state = RcfdStateOpen fd⌝ ∗
        rcfd_tokens_auth γ qs ∗
        unix_fd_model fd (DfracOwn q) chars
    | RcfdLstateClosingUsers =>
        ∃ q qs fn,
        ⌜ops = size qs ∧ 0 < size qs ∧ set_fold Qp.add q qs = 1%Qp⌝ ∗
        ⌜state = RcfdStateClosing fn⌝ ∗
        rcfd_tokens_auth γ qs ∗
        unix_fd_model fd (DfracOwn q) chars ∗
        (unix_fd_model fd (DfracOwn 1) chars -∗ WP fn #() {{ res, ⌜res = #()⌝ }})
    | RcfdLstateClosingNoUsers =>
        ∃ fn,
        ⌜state = RcfdStateClosing fn⌝ ∗
        WP fn #() {{ res, ⌜res = #()⌝ }}
    end.
  Definition rcfd_inv t fd chars : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv nroot (rcfd_inv_inner l γ fd chars).

  Definition rcfd_token t q : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    rcfd_tokens_frag γ q.

  Definition rcfd_closing t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    rcfd_lstate_lb γ RcfdLstateClosingUsers.

  #[global] Instance rcfd_inv_timeless t q :
    Timeless (rcfd_token t q).
  Proof.
    apply _.
  Qed.
  #[global] Instance rcfd_inv_persistent t fd chars :
    Persistent (rcfd_inv t fd chars).
  Proof.
    apply _.
  Qed.

  #[global] Instance rcfd_token_timeless t q :
    Timeless (rcfd_token t q).
  Proof.
    apply _.
  Qed.

  #[global] Instance rcfd_closing_timeless t :
    Timeless (rcfd_closing t).
  Proof.
    apply _.
  Qed.
  #[global] Instance rcfd_closing_persistent t :
    Persistent (rcfd_closing t).
  Proof.
    apply _.
  Qed.

  #[local] Lemma rcfd_tokens_alloc :
    ⊢ |==>
      ∃ γ_tokens,
      rcfd_tokens_auth' γ_tokens ∅.
  Proof.
    apply auth_gmultiset_alloc.
  Qed.
  #[local] Lemma rcfd_tokens_elem_of γ qs q :
    rcfd_tokens_auth γ qs -∗
    rcfd_tokens_frag γ q -∗
    ⌜q ∈ qs⌝.
  Proof.
    apply auth_gmultiset_elem_of.
  Qed.
  #[local] Lemma rcfd_tokens_update_alloc {γ qs} q :
    rcfd_tokens_auth γ qs ⊢ |==>
      rcfd_tokens_auth γ (qs ⊎ {[+q+]}) ∗
      rcfd_tokens_frag γ q.
  Proof.
    apply auth_gmultiset_update_alloc_singleton.
  Qed.
  #[local] Lemma rcfd_tokens_update_dealloc γ qs q :
    rcfd_tokens_auth γ qs -∗
    rcfd_tokens_frag γ q ==∗
    rcfd_tokens_auth γ (qs ∖ {[+q+]}).
  Proof.
    apply auth_gmultiset_update_dealloc.
  Qed.

  #[local] Lemma rcfd_lstate_alloc :
    ⊢ |==>
      ∃ γ_lstate,
      rcfd_lstate_auth' γ_lstate RcfdLstateOpen.
  Proof.
    apply mono_state_alloc.
  Qed.
  #[local] Lemma rcfd_lstate_lb_get γ lstate :
    rcfd_lstate_auth γ lstate ⊢
    rcfd_lstate_lb γ lstate.
  Proof.
    apply mono_state_lb_get.
  Qed.
  #[local] Lemma rcfd_lstate_lb_mono {γ lstate} lstate' :
    rcfd_lstep lstate' lstate →
    rcfd_lstate_lb γ lstate ⊢
    rcfd_lstate_lb γ lstate'.
  Proof.
    apply mono_state_lb_mono'.
  Qed.
  #[local] Lemma rcfd_lstate_valid γ lstate lstate' :
    rcfd_lstate_auth γ lstate -∗
    rcfd_lstate_lb γ lstate' -∗
    ⌜rtc rcfd_lstep lstate' lstate⌝.
  Proof.
    apply mono_state_valid.
  Qed.
  #[local] Lemma rcfd_lstate_valid_closing_users γ lstate :
    rcfd_lstate_auth γ lstate -∗
    rcfd_lstate_lb γ RcfdLstateClosingUsers -∗
    ⌜lstate = RcfdLstateClosingUsers ∨ lstate = RcfdLstateClosingNoUsers⌝.
  Proof.
    iIntros "Hlstate_auth Hlstate_lb".
    iDestruct (rcfd_lstate_valid with "Hlstate_auth Hlstate_lb") as %Hlsteps.
    iPureIntro.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
  Qed.
  #[local] Lemma rcfd_lstate_valid_closing_no_users γ lstate :
    rcfd_lstate_auth γ lstate -∗
    rcfd_lstate_lb γ RcfdLstateClosingNoUsers -∗
    ⌜lstate = RcfdLstateClosingNoUsers⌝.
  Proof.
    iIntros "Hlstate_auth Hlstate_lb".
    iDestruct (rcfd_lstate_valid with "Hlstate_auth Hlstate_lb") as %Hlsteps.
    iPureIntro.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
  Qed.
  #[local] Lemma rcfd_lstate_update {γ lstate} lstate' :
    rcfd_lstep lstate lstate' →
    rcfd_lstate_auth γ lstate ⊢ |==>
    rcfd_lstate_auth γ lstate'.
  Proof.
    apply mono_state_update'.
  Qed.

  Lemma rcfd_make_spec fd chars :
    {{{
      unix_fd_model fd (DfracOwn 1) chars
    }}}
      rcfd_make fd
    {{{ t,
      RET t;
      rcfd_inv t fd chars
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_alloc l_state as "Hstate". iMod (mapsto_persist with "Hstate") as "Hstate".
    iApply wp_fupd.
    wp_smart_apply (record2_make_spec with "[//]"). iIntros "%l (Hl & Hmeta)".
    iDestruct (record2_model_eq_1 with "Hl") as "(Hops & Hfd)".
    iMod rcfd_tokens_alloc as "(%γ_tokens & Htokens_auth)".
    iMod rcfd_lstate_alloc as "(%γ_lstate & Hlstate_auth)".
    pose γ := {|
      rcfd_meta_tokens := γ_tokens ;
      rcfd_meta_lstate := γ_lstate ;
      rcfd_meta_open_state := l_state ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "Hmeta"; first done.
    iApply "HΦ". iExists l, γ. iStep 2.
    iApply inv_alloc. iExists (RcfdStateOpen fd). iStep 5. iExists 1%Qp, ∅. iSteps.
  Qed.

  #[local] Lemma rcfd_put_spec' l γ fd chars :
    {{{
      inv nroot (rcfd_inv_inner l γ fd chars) ∗
      ( ( ∃ q,
          rcfd_tokens_frag γ q ∗
          unix_fd_model fd (DfracOwn q) chars
        )
      ∨ rcfd_lstate_lb γ RcfdLstateClosingNoUsers
      )
    }}}
      rcfd_put #l
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".

    wp_rec. wp_pures.

    wp_bind (FAA _ _).
    iInv "Hinv" as "(%state1 & %lstate1 & %ops1 & %l_state1 & Hops1 & Hfd1 & Hstate1 & Hlstate_auth & Hlstate1)".
    wp_faa.
    iSplitR "HΦ".
    { iDestruct "H" as "[(%q & Htokens_frag & Hmodel) | #Hlstate_lb]".
      - destruct lstate1.
        + iDestruct "Hlstate1" as "(%q' & %qs & (-> & %Hqs) & (-> & ->) & Htokens_auth & Hmodel')".
          iDestruct (rcfd_tokens_elem_of with "Htokens_auth Htokens_frag") as %Hq.
          iExists (RcfdStateOpen _). iStep 4. iExists (q + q')%Qp, (qs ∖ {[+q+]}).
          iSplitR; [iSplitR; iPureIntro | iSplitR; [| iSplitR "Hmodel Hmodel'"]].
          * assert (qs ≠ ∅) as Hqs_size%gmultiset_size_non_empty_iff by multiset_solver.
            rewrite gmultiset_size_difference; last multiset_solver.
            rewrite gmultiset_size_singleton. lia.
          * rewrite (gmultiset_disj_union_difference' q qs) // gmultiset_set_fold_disj_union gmultiset_set_fold_singleton // in Hqs.
          * iSteps.
          * iMod (rcfd_tokens_update_dealloc with "Htokens_auth Htokens_frag") as "$". iSteps.
          * iCombine "Hmodel Hmodel'" as "$". iSteps.
        + iDestruct "Hlstate1" as "(%q' & %qs & %fn1 & (-> & %Hqs_size & %Hqs) & -> & Htokens_auth & Hmodel' & Hfn1)".
          iDestruct (rcfd_tokens_elem_of with "Htokens_auth Htokens_frag") as %Hq.
          destruct (decide (size qs = 1)) as [Hqs_size' | Hqs_size'].
          * apply gmultiset_size_1_elem_of in Hqs_size' as (q_ & ->%leibniz_equiv). rewrite gmultiset_set_fold_singleton in Hqs.
            apply gmultiset_elem_of_singleton in Hq as <-.
            iMod (rcfd_tokens_update_dealloc with "Htokens_auth Htokens_frag") as "Htokens_auth".
            rewrite gmultiset_difference_diag.
            iMod (rcfd_lstate_update RcfdLstateClosingNoUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
            iCombine "Hmodel Hmodel'" as "Hmodel". rewrite Hqs. iDestruct ("Hfn1" with "Hmodel") as "Hfn1".
            iExists (RcfdStateClosing _). iStep 5. done.
          * iMod (rcfd_tokens_update_dealloc with "Htokens_auth Htokens_frag") as "Htokens_auth".
            iCombine "Hmodel Hmodel'" as "Hmodel".
            iExists (RcfdStateClosing _). iStep 4. iExists (q + q')%Qp, (qs ∖ {[+q+]}). iSteps; iPureIntro.
            -- rewrite gmultiset_size_difference; last multiset_solver.
               rewrite gmultiset_size_singleton. lia.
            -- rewrite gmultiset_size_difference; last multiset_solver.
               rewrite gmultiset_size_singleton. lia.
            -- rewrite (gmultiset_disj_union_difference' q qs) // gmultiset_set_fold_disj_union gmultiset_set_fold_singleton // in Hqs.
        + iDestruct "Hlstate1" as "(%fn1 & -> & Hfn1)".
          iExists (RcfdStateClosing _). iStep 5. done.
      - iDestruct (rcfd_lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %->.
        iDestruct "Hlstate1" as "(%fn1 & -> & Hfn1)".
        iExists (RcfdStateClosing _). iStep 5. done.
    }
    iModIntro. clear.

    wp_pures. destruct (decide (ops1 = 1)) as [-> | Hops]; wp_pures; last iSteps.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%state2 & %lstate2 & %ops2 & %l_state2 & Hops2 & Hfd2 & #Hstate2 & Hlstate_auth & Hlstate2)".
    wp_load.
    destruct (decide (lstate2 = RcfdLstateOpen)) as [-> | Hlstate2].

    - iDestruct "Hlstate2" as "(%q & %qs & (-> & %Hqs) & (-> & ->) & Htokens_auth & Hmodel)".
      iSplitR "HΦ". { iExists (RcfdStateOpen _). iSteps. }
      iSteps.

    - iAssert (∃ fn2, ⌜state2 = RcfdStateClosing fn2⌝ ∗ rcfd_lstate_lb γ RcfdLstateClosingUsers)%I as "(%fn2 & -> & #Hlstate_lb)".
      { destruct lstate2; first done.
        - iDestruct "Hlstate2" as "(%q & %qs & %fn2 & _ & -> & _)".
          iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "$".
          iSteps.
        - iDestruct "Hlstate2" as "(%fn2 & -> & _)".
          iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
          iDestruct (rcfd_lstate_lb_mono RcfdLstateClosingUsers with "Hlstate_lb") as "Hlstate_lb"; first done.
          iSteps.
      }
      iSplitR "HΦ". { iExists (RcfdStateClosing _). iSteps. }
      iModIntro. clear.

      wp_load. wp_pures.

      wp_bind (!_)%E.
      iInv "Hinv" as "(%state3 & %lstate3 & %ops3 & %l_state3 & Hops3 & Hfd3 & #Hstate3 & Hlstate_auth & Hlstate3)".
      wp_load.
      iDestruct (rcfd_lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].

      + iDestruct "Hlstate3" as "(%q & %qs & %fn3 & (-> & %Hqs_size & %Hqs) & -> & Htokens_auth & Hmodel & Hfn3)".
        iSplitR "HΦ". { iExists (RcfdStateClosing _). iSteps. }
        iModIntro. clear- Hqs_size.

        wp_pures. rewrite bool_decide_eq_true_2; last lia. wp_pures.

        iSteps.

      + iDestruct "Hlstate3" as "(%fn3 & -> & Hfn3)".
        iClear "Hlstate_lb". iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "HΦ". { iExists (RcfdStateClosing _). iStep 5. done. }
        iModIntro. clear.

        wp_pures. case_bool_decide as Hops3; wp_pures; first iSteps.

        wp_rec. wp_alloc closed as "Hclosed". wp_pures.

        wp_bind (CmpXchg _ _ _).
        iInv "Hinv" as "(%state4 & %lstate4 & %ops4 & %l_state4 & Hops4 & Hfd4 & #Hstate4 & Hlstate_auth & Hlstate4)".
        wp_cmpxchg as [= <-] | Hcmpxchg; last iSteps.
        iDestruct (rcfd_lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %->.
        iDestruct "Hlstate4" as "(%fn4 & -> & Hfn4)".
        iDestruct (mapsto_agree with "Hstate2 Hstate4") as %[= <-]%(inj _).
        iSplitR "Hfn4 HΦ". { iExists (RcfdStateClosing _). iSteps. }
        iSteps.
  Qed.
  #[local] Lemma rcfd_put_spec t fd chars q :
    {{{
      rcfd_inv t fd chars ∗
      rcfd_token t q ∗
      unix_fd_model fd (DfracOwn q) chars
    }}}
      rcfd_put t
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %Heq & _Hmeta & Htokens_frag) & Hmodel) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iApply (rcfd_put_spec' with "[$Hinv Htokens_frag Hmodel] HΦ").
    iSteps.
  Qed.

  #[local] Lemma rcfd_get_spec t fd chars :
    {{{
      rcfd_inv t fd chars
    }}}
      rcfd_get t
    {{{ o,
      RET (o : val);
      match o with
      | None =>
          True
      | Some fd_ =>
          ∃ q,
          ⌜fd_ = fd⌝ ∗
          rcfd_token t q ∗
          unix_fd_model fd (DfracOwn q) chars
      end
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    wp_rec. wp_pures.

    wp_bind (FAA _ _).
    iInv "Hinv" as "(%state1 & %lstate1 & %ops1 & %l_state1 & Hops1 & Hfd1 & Hstate1 & Hlstate_auth & Hlstate1)".
    wp_faa.
    iAssert (|==>
      rcfd_inv_inner l γ fd chars ∗
      ( ( ∃ q,
          rcfd_tokens_frag γ q ∗
          unix_fd_model fd (DfracOwn q) chars
        )
      ∨ rcfd_lstate_lb γ RcfdLstateClosingNoUsers
      )
    )%I with "[- HΦ]" as ">($ & H)".
    { destruct lstate1.
      - iDestruct "Hlstate1" as "(%q & %qs & (-> & %Hqs) & (-> & ->) & Htokens_auth & Hmodel)".
        iMod (rcfd_tokens_update_alloc (q / 2) with "Htokens_auth") as "(Htokens_auth & Htokens_frag)".
        iDestruct "Hmodel" as "(Hmodel1 & Hmodel2)".
        iSplitR "Htokens_frag Hmodel2"; last iSteps.
        iExists (RcfdStateOpen _). iStep 4. iExists (q / 2)%Qp, (qs ⊎ {[+q / 2+]})%Qp. iSteps; iPureIntro.
        + rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
        + rewrite (comm (⊎)) gmultiset_set_fold_disj_union gmultiset_set_fold_singleton Qp.div_2 //.
      - iDestruct "Hlstate1" as "(%q & %qs & %fn1 & (-> & %Hqs_size & %Hqs) & -> & Htokens_auth & Hmodel & Hfn1)".
        iMod (rcfd_tokens_update_alloc (q / 2) with "Htokens_auth") as "(Htokens_auth & Htokens_frag)".
        iDestruct "Hmodel" as "(Hmodel1 & Hmodel2)".
        iSplitR "Htokens_frag Hmodel2"; last iSteps.
        iExists (RcfdStateClosing _). iStep 4. iExists (q / 2)%Qp, (qs ⊎ {[+q / 2+]})%Qp. iSteps; iPureIntro.
        + rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
        + rewrite gmultiset_size_disj_union. lia.
        + rewrite (comm (⊎)) gmultiset_set_fold_disj_union gmultiset_set_fold_singleton Qp.div_2 //.
      - iDestruct "Hlstate1" as "(%fn1 & -> & Hfn1)".
        iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitL; last iSteps.
        iExists (RcfdStateClosing _). iSteps.
    }
    iModIntro. wp_pures. clear.

    wp_bind (!#l.[fd])%E.
    iInv "Hinv" as "(%state2 & %lstate2 & %ops2 & %l_state2 & Hops2 & Hfd2 & #Hstate2 & Hlstate_auth & Hlstate2)".
    wp_load.
    destruct (decide (lstate2 = RcfdLstateOpen)) as [-> | Hlstate2].

    - iDestruct "Hlstate2" as "(%q & %qs & (-> & %Hqs) & (-> & ->) & Htokens_auth & Hmodel)".
      iDestruct "H" as "[(%q' & Htokens_frag & Hmodel') | Hlstate_lb]"; last first.
      { iDestruct (rcfd_lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %?. done. }
      iSplitR "Htokens_frag Hmodel' HΦ". { iExists (RcfdStateOpen _). iSteps. }
      iSteps. iApply ("HΦ" $! (Some _)). iSteps.

    - iAssert ⌜∃ fn2, state2 = RcfdStateClosing fn2⌝%I as %(fn2 & ->).
      { destruct lstate2; iDecompose "Hlstate2"; iSteps. }
      iSplitR "H HΦ". { iExists (RcfdStateClosing fn2). iSteps. }
      iModIntro. clear.

      wp_load.
      wp_smart_apply (rcfd_put_spec' with "[$Hinv $H]").
      iSteps. iApply ("HΦ" $! None). iSteps.
  Qed.

  #[local] Lemma rcfd_close_spec' closing t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      if closing then
        rcfd_closing t
      else
        True
    }}}
      rcfd_close t
    {{{ b,
      RET #b;
      if closing then
        ⌜b = false⌝
      else
        rcfd_closing t
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%state1 & %lstate1 & %ops1 & %l_state1 & Hops1 & Hfd1 & #Hstate1 & Hlstate_auth & Hlstate1)".
    wp_load.
    destruct (decide (lstate1 = RcfdLstateOpen)) as [-> | Hlstate1].

    - iDestruct "Hlstate1" as "(%q & %qs & (-> & %Hqs) & (-> & ->) & Htokens_auth & Hmodel)".
      destruct closing; last iClear "Hclosing".
      { iDestruct "Hclosing" as "(%_l & %_γ & %Heq & _Hmeta & Hlstate_lb)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (rcfd_lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[[=] | [=]].
      }
      iSplitR "HΦ". { iExists (RcfdStateOpen _). iSteps. }
      iModIntro. clear.

      wp_load.
      wp_alloc l_state as "Hstate". iMod (mapsto_persist with "Hstate") as "#Hstate".
      wp_pures.

      wp_bind (CmpXchg _ _ _).
      iInv "Hinv" as "(%state2 & %lstate2 & %ops2 & %l_state2 & Hops2 & Hfd2 & #Hstate2 & Hlstate_auth & Hlstate2)".
      wp_cmpxchg as [= <-] | Hcmpxchg.

      + iDestruct (mapsto_agree with "Hstate1 Hstate2") as %[= <-]%(inj _).
        destruct (decide (lstate2 = RcfdLstateOpen)) as [-> | Hlstate2]; last first.
        { destruct lstate2; iDecompose "Hlstate2"; iSteps. }
        iDestruct "Hlstate2" as "(%q & %qs & (-> & %Hqs) & _ & Htokens_auth & Hmodel)".
        iMod (rcfd_lstate_update RcfdLstateClosingUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
        iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "HΦ".
        { destruct (decide (size qs = 0)) as [Hqs_size | Hqs_size].
          - apply gmultiset_size_empty_iff in Hqs_size as ->.
            rewrite gmultiset_set_fold_empty in Hqs. rewrite {}Hqs.
            iMod (rcfd_lstate_update RcfdLstateClosingNoUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
            iExists (RcfdStateClosing _). iSteps. iModIntro.
            wp_apply (unix_close_spec with "[$]").
            iSteps.
          - iExists (RcfdStateClosing _). iSteps. iModIntro.
            wp_apply (unix_close_spec with "[$]").
            iSteps.
        }
        iModIntro. clear.

        wp_pures.

        wp_bind (!_)%E.
        iInv "Hinv" as "(%state3 & %lstate3 & %ops3 & %l_state3 & Hops3 & Hfd3 & #Hstate3 & Hlstate_auth & Hlstate3)".
        wp_load.
        destruct (decide (ops3 = 0)) as [-> | Hops3]; last iSteps.
        iDestruct (rcfd_lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].
        { iDestruct "Hlstate3" as "(%q & %qs & %fn3 & (% & % & _) & _)". lia. }
        iDestruct "Hlstate3" as "(%fn3 & -> & Hfn3)".
        iRename "Hlstate_lb" into "Hlstate_lb'". iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "HΦ". { iExists (RcfdStateClosing _). iStep 5. done. }
        iModIntro. clear.

        wp_pures.

        wp_rec. wp_alloc closed as "Hclosed". wp_pures.

        wp_bind (CmpXchg _ _ _).
        iInv "Hinv" as "(%state4 & %lstate4 & %ops4 & %l_state4 & Hops4 & Hfd4 & #Hstate4 & Hlstate_auth & Hlstate4)".
        wp_cmpxchg as [= <-] | Hcmpxchg; last iSteps.

        iDestruct (rcfd_lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %->.
        iDestruct "Hlstate4" as "(%fn4 & -> & Hfn4)".
        iDestruct (mapsto_agree with "Hstate Hstate4") as %Hfn4. simpl in Hfn4. apply (inj _) in Hfn4 as <-.
        iSplitR "Hfn4 HΦ". { iExists (RcfdStateClosing _). iSteps. }
        iModIntro. clear.

        do 2 wp_pure.
        wp_apply (wp_wand with "Hfn4").
        iSteps.

      + iAssert (⌜∃ fn2, state2 = RcfdStateClosing fn2⌝ ∗ rcfd_lstate_lb γ RcfdLstateClosingUsers)%I as "((%fn2 & ->) & #Hlstate_lb)".
        { destruct lstate2; iDecompose "Hlstate2".
          - iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "$".
            iSteps.
          - iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iDestruct (rcfd_lstate_lb_mono with "Hlstate_lb") as "$"; first done.
            iSteps.
        }
        iSplitR "HΦ". { iExists (RcfdStateClosing _). iSteps. }
        iSteps.

    - iAssert (⌜∃ fn1, state1 = RcfdStateClosing fn1⌝ ∗ rcfd_lstate_lb γ RcfdLstateClosingUsers)%I as "((%fn1 & ->) & #Hlstate_lb)".
      { destruct lstate1; iDecompose "Hlstate1".
        - iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "$".
          iSteps.
        - iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
          iDestruct (rcfd_lstate_lb_mono with "Hlstate_lb") as "$"; first done.
          iSteps.
      }
      iSplitR "HΦ". { iExists (RcfdStateClosing _). iSteps. }
      iSteps. destruct closing; iSteps.
  Qed.
  Lemma rcfd_close_spec t fd chars :
    {{{
      rcfd_inv t fd chars
    }}}
      rcfd_close t
    {{{ b,
      RET #b;
      rcfd_closing t
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (rcfd_close_spec' false with "[$Hinv]").
    iSteps.
  Qed.
  Lemma rcfd_close_spec_closed t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      rcfd_closing t
    }}}
      rcfd_close t
    {{{
      RET #false; True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_close_spec' true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_remove_spec' closing {mutex : mutex Σ} (condition : condition mutex) t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      if closing then
        rcfd_closing t
      else
        True
    }}}
      rcfd_remove condition t
    {{{ o,
      RET (o : val);
      if closing then
        ⌜o = None⌝
      else
        rcfd_closing t ∗
        match o with
        | None =>
            True
        | Some fd' =>
            ⌜fd' = fd⌝ ∗
            unix_fd_model fd (DfracOwn 1) chars
        end
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%state1 & %lstate1 & %ops1 & %l_state1 & Hops1 & Hfd1 & #Hstate1 & Hlstate_auth & Hlstate1)".
    wp_load.
    destruct (decide (lstate1 = RcfdLstateOpen)) as [-> | Hlstate1].

    - iDestruct "Hlstate1" as "(%q & %qs & (-> & %Hqs) & (-> & ->) & Htokens_auth & Hmodel)".
      destruct closing; last iClear "Hclosing".
      { iDestruct "Hclosing" as "(%_l & %_γ & %Heq & _Hmeta & Hlstate_lb)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (rcfd_lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[[=] | [=]].
      }
      iSplitR "HΦ". { iExists (RcfdStateOpen _). iSteps. }
      iModIntro. clear.

      wp_load.
      wp_alloc flag as "Hflag".
      wp_smart_apply (channel1_create_spec _ (unix_fd_model fd (DfracOwn 1) chars) with "[//]"). iIntros "%chan (#Hchan_inv & Hchan_producer & Hchan_consumer)".
      wp_alloc l_state as "Hstate". iMod (mapsto_persist with "Hstate") as "#Hstate".
      wp_pures.

      wp_bind (CmpXchg _ _ _).
      iInv "Hinv" as "(%state2 & %lstate2 & %ops2 & %l_state2 & Hops2 & Hfd2 & #Hstate2 & Hlstate_auth & Hlstate2)".
      wp_cmpxchg as [= <-] | Hcmpxchg.

      + iDestruct (mapsto_agree with "Hstate1 Hstate2") as %[= <-]%(inj _).
        destruct (decide (lstate2 = RcfdLstateOpen)) as [-> | Hlstate2]; last first.
        { destruct lstate2; iDecompose "Hlstate2"; iSteps. }
        iDestruct "Hlstate2" as "(%q & %qs & (-> & %Hqs) & _ & Htokens_auth & Hmodel)".
        iMod (rcfd_lstate_update RcfdLstateClosingUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
        iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "Hchan_consumer HΦ".
        { destruct (decide (size qs = 0)) as [Hqs_size | Hqs_size].
          - apply gmultiset_size_empty_iff in Hqs_size as ->.
            rewrite gmultiset_set_fold_empty in Hqs. rewrite {}Hqs.
            iMod (rcfd_lstate_update RcfdLstateClosingNoUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
            iExists (RcfdStateClosing _). iStep 9. iModIntro.
            wp_apply (channel1_signal_spec with "[$Hchan_inv $Hchan_producer $Hmodel]").
            iSteps.
          - iExists (RcfdStateClosing _). iStep 11 as "Hmodel". iModIntro.
            wp_apply (channel1_signal_spec with "[$Hchan_inv $Hchan_producer $Hmodel]").
            iSteps.
        }
        iModIntro. clear.

        wp_smart_apply (channel1_wait_spec with "[$Hchan_inv $Hchan_consumer]"). iIntros "Hmodel".
        iSteps. iApply ("HΦ" $! (Some _)). iSteps.

      + iAssert (⌜∃ fn2, state2 = RcfdStateClosing fn2⌝ ∗ rcfd_lstate_lb γ RcfdLstateClosingUsers)%I as "((%fn2 & ->) & #Hlstate_lb)".
        { destruct lstate2; iDecompose "Hlstate2".
          - iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "$".
            iSteps.
          - iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iDestruct (rcfd_lstate_lb_mono with "Hlstate_lb") as "$"; first done.
            iSteps.
        }
        iSplitR "HΦ". { iExists (RcfdStateClosing _). iSteps. }
        iSteps. iApply ("HΦ" $! None). iSteps.

    - iAssert (⌜∃ fn1, state1 = RcfdStateClosing fn1⌝ ∗ rcfd_lstate_lb γ RcfdLstateClosingUsers)%I as "((%fn1 & ->) & #Hlstate_lb)".
      { destruct lstate1; iDecompose "Hlstate1".
        - iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "$".
          iSteps.
        - iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
          iDestruct (rcfd_lstate_lb_mono with "Hlstate_lb") as "$"; first done.
          iSteps.
      }
      iSplitR "HΦ". { iExists (RcfdStateClosing _). iSteps. }
      iSteps. iApply ("HΦ" $! None). destruct closing; iSteps.
  Qed.
  Lemma rcfd_remove_spec {mutex : mutex Σ} (condition : condition mutex) t fd chars :
    {{{
      rcfd_inv t fd chars
    }}}
      rcfd_remove condition t
    {{{ o,
      RET (o : val);
      rcfd_closing t ∗
      match o with
      | None =>
          True
      | Some fd' =>
          ⌜fd' = fd⌝ ∗
          unix_fd_model fd (DfracOwn 1) chars
      end
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (rcfd_remove_spec' false with "[$Hinv]").
    iSteps.
  Qed.
  Lemma rcfd_remove_spec_closing closing {mutex : mutex Σ} (condition : condition mutex) t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      rcfd_closing t
    }}}
      rcfd_remove condition t
    {{{
      RET &&None; True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_remove_spec' true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.

  Lemma rcfd_use_spec Ψ t fd chars (closed open : val) :
    {{{
      rcfd_inv t fd chars ∗
      WP closed #() {{ res,
        ⌜res = #()⌝ ∗
        Ψ false
      }} ∗
      ( ∀ q,
        rcfd_token t q -∗
        unix_fd_model fd (DfracOwn q) chars -∗
        WP open fd {{ res,
          ⌜res = #()⌝ ∗
          rcfd_token t q ∗
          unix_fd_model fd (DfracOwn q) chars ∗
          Ψ true
        }}
      )
    }}}
      rcfd_use t closed open
    {{{ b,
      RET #();
      Ψ b
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hclosed & Hopen) HΦ".
    wp_rec.
    wp_smart_apply (rcfd_get_spec with "Hinv"). iIntros ([]); last iSteps.
    iIntros "(%q & -> & Htoken & Hmodel)".
    wp_smart_apply (wp_wand with "(Hopen Htoken Hmodel)"). iIntros "%res (-> & Htoken & Hmodel & HΨ)".
    wp_smart_apply (rcfd_put_spec with "[$Hinv $Htoken $Hmodel]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_is_open_spec' closing t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      if closing then
        rcfd_closing t
      else
        True
    }}}
      rcfd_is_open t
    {{{ b,
      RET #b;
      if closing then
        ⌜b = false⌝
      else
        if b then
          True
        else
          rcfd_closing t
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (!#l.[fd])%E.
    iInv "Hinv" as "(%state & %lstate & %ops & %l_state & Hops & Hfd & #Hstate & Hlstate_auth & Hlstate)".
    wp_load.
    destruct closing; last iClear "Hclosing".

    - iDestruct "Hclosing" as "(%_l & %_γ & %Heq & _Hmeta & Hlstate_lb)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iAssert ⌜∃ fn, state = RcfdStateClosing fn⌝%I as %(fn & ->).
      { iDestruct (rcfd_lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].
        all: iDecompose "Hlstate"; iSteps.
      }
      iSplitR "HΦ". { iExists (RcfdStateClosing _). iSteps. }
      iSteps.

    - destruct state.

      + iSplitR "HΦ". { iExists (RcfdStateOpen _). iSteps. }
        iSteps.

      + iAssert (rcfd_lstate_lb γ RcfdLstateClosingUsers) as "#Hlstate_lb".
        { destruct lstate; iDecompose "Hlstate".
          - iApply (rcfd_lstate_lb_get with "Hlstate_auth").
          - iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iApply (rcfd_lstate_lb_mono with "Hlstate_lb"); first done.
        }
        iSplitR "HΦ". { iExists (RcfdStateClosing _). iSteps. }
        iSteps.
  Qed.
  Lemma rcfd_is_open_spec t fd chars :
    {{{
      rcfd_inv t fd chars
    }}}
      rcfd_is_open t
    {{{ b,
      RET #b;
      if b then
        True
      else
        rcfd_closing t
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (rcfd_is_open_spec' false with "[$Hinv]").
    iSteps.
  Qed.
  Lemma rcfd_is_open_spec_closed t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      rcfd_closing t
    }}}
      rcfd_is_open t
    {{{
      RET #false; True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_is_open_spec' true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_peek_spec' closing t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      if closing then
        rcfd_closing t
      else
        True
    }}}
      rcfd_peek t
    {{{ o,
      RET (o : val);
      if closing then
        ⌜o = None⌝
      else
        match o with
        | None =>
            rcfd_closing t
        | Some fd' =>
            ⌜fd' = fd⌝
        end
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (!#l.[fd])%E.
    iInv "Hinv" as "(%state & %lstate & %ops & %l_state & Hops & Hfd & #Hstate & Hlstate_auth & Hlstate)".
    wp_load.
    destruct closing; last iClear "Hclosing".

    - iDestruct "Hclosing" as "(%_l & %_γ & %Heq & _Hmeta & Hlstate_lb)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iAssert ⌜∃ fn, state = RcfdStateClosing fn⌝%I as %(fn & ->).
      { iDestruct (rcfd_lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].
        all: iDecompose "Hlstate"; iSteps.
      }
      iSplitR "HΦ". { iExists (RcfdStateClosing _). iSteps. }
      iSteps. iApply ("HΦ" $! None). iSteps.

    - destruct state as [_fd |].

      + iAssert ⌜_fd = fd⌝%I as %->.
        { destruct lstate; iDecompose "Hlstate". iSteps. }
        iSplitR "HΦ". { iExists (RcfdStateOpen _). iSteps. }
        iSteps. iApply ("HΦ" $! (Some _)). iSteps.

      + iAssert (rcfd_lstate_lb γ RcfdLstateClosingUsers) as "#Hlstate_lb".
        { destruct lstate; iDecompose "Hlstate".
          - iApply (rcfd_lstate_lb_get with "Hlstate_auth").
          - iDestruct (rcfd_lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iApply (rcfd_lstate_lb_mono with "Hlstate_lb"); first done.
        }
        iSplitR "HΦ". { iExists (RcfdStateClosing _). iSteps. }
        iSteps. iApply ("HΦ" $! None). iSteps.
  Qed.
  Lemma rcfd_peek_spec t fd chars :
    {{{
      rcfd_inv t fd chars
    }}}
      rcfd_peek t
    {{{ o,
      RET (o : val);
      match o with
      | None =>
          rcfd_closing t
      | Some fd' =>
          ⌜fd' = fd⌝
      end
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (rcfd_peek_spec' false with "[$Hinv]").
    iSteps.
  Qed.
  Lemma rcfd_peek_spec_closed t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      rcfd_closing t
    }}}
      rcfd_peek t
    {{{
      RET &&None; True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_peek_spec' true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.
End rcfd_G.

#[global] Opaque rcfd_make.
#[global] Opaque rcfd_close.
#[global] Opaque rcfd_use.
#[global] Opaque rcfd_is_open.
#[global] Opaque rcfd_peek.

#[global] Opaque rcfd_inv.
#[global] Opaque rcfd_token.
#[global] Opaque rcfd_closing.
