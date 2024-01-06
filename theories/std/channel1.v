From heap_lang Require Import
  prelude.
From heap_lang.iris.base_logic Require Import
  lib.oneshot
  lib.excl.
From heap_lang.language Require Import
  notations
  diaframe.
From heap_lang.std Require Import
  record3.
From heap_lang.std Require Export
  condition.

Implicit Types b : bool.
Implicit Types l : loc.

#[local] Notation "t '.[flag]'" :=
  t.[0]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[mutex]'" :=
  t.[1]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[condition]'" :=
  t.[2]%stdpp
( at level 5
) : stdpp_scope.
#[local] Notation "t '.[flag]'" :=
  t.[#0]%E
( at level 5
) : expr_scope.
#[local] Notation "t '.[mutex]'" :=
  t.[#1]%E
( at level 5
) : expr_scope.
#[local] Notation "t '.[condition]'" :=
  t.[#2]%E
( at level 5
) : expr_scope.

Section condition.
  Context `{heap_GS : !heapGS Σ} {mutex : mutex Σ} (condition : condition mutex).

  Definition channel1_create : val :=
    λ: <>,
      let: "t" := record3_make #false #() #() in
      "t".[mutex] <- mutex.(mutex_create) #() ;;
      "t".[condition] <- condition.(condition_create) #() ;;
      "t".

  Definition channel1_signal : val :=
    λ: "t",
      mutex.(mutex_protect) !"t".[mutex] (λ: <>,
        "t".[flag] <- #true
      ) ;;
      condition.(condition_signal) !"t".[condition].

  Definition channel1_wait : val :=
    λ: "t",
      let: "mtx" := !"t".[mutex] in
      let: "cond" := !"t".[condition] in
      mutex.(mutex_protect) "mtx" (λ: <>,
        condition.(condition_wait_until) "cond" "mtx" (λ: <>, !"t".[flag])
      ).
End condition.

Class Channel1G Σ `{heap_GS : !heapGS Σ} := {
  #[local] channel1_G_producer_G :: OneshotG Σ unit unit ;
  #[local] channel1_G_consumer_G :: ExclG Σ unitO ;
}.

Definition channel1_Σ := #[
  oneshot_Σ unit unit ;
  excl_Σ unitO
].
#[global] Instance subG_channel1_Σ Σ `{heap_GS : !heapGS Σ} :
  subG channel1_Σ Σ →
  Channel1G Σ .
Proof.
  solve_inG.
Qed.

Section channel1_G.
  Context `{channel1_G : Channel1G Σ}.
  Context {mutex : mutex Σ} (condition : condition mutex).

  Record channel1_meta := {
    channel1_meta_producer : gname ;
    channel1_meta_consumer : gname ;
  }.
  Implicit Types γ : channel1_meta.

  #[local] Instance channel1_meta_eq_dec : EqDecision channel1_meta :=
    ltac:(solve_decision).
  #[local] Instance channel1_meta_countable :
    Countable channel1_meta.
  Proof.
    pose encode γ := (
      γ.(channel1_meta_producer),
      γ.(channel1_meta_consumer)
    ).
    pose decode := λ '(γ_producer, γ_consumer), {|
      channel1_meta_producer := γ_producer ;
      channel1_meta_consumer := γ_consumer ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition channel1_inv_inner l γ P : iProp Σ :=
    ∃ b,
    l.[flag] ↦ #b ∗
    if b then
      oneshot_shot γ.(channel1_meta_producer) () ∗
      ( P
      ∨ excl γ.(channel1_meta_consumer) ()
      )
    else
      oneshot_pending γ.(channel1_meta_producer) (DfracOwn (1/3)) ().
  #[local] Definition channel1_inv t P : iProp Σ :=
    ∃ l γ mtx cond,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[mutex] ↦□ mtx ∗
    mutex.(mutex_inv) mtx (channel1_inv_inner l γ P) ∗
    l.[condition] ↦□ cond ∗
    condition.(condition_inv) cond.

  Definition channel1_producer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    oneshot_pending γ.(channel1_meta_producer) (DfracOwn (2/3)) ().

  Definition channel1_consumer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    excl γ.(channel1_meta_consumer) ().

  #[global] Instance channel1_inv_persistent t P :
    Persistent (channel1_inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance channel1_producer_timeless t :
    Timeless (channel1_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance channel1_consumer_timeless t :
    Timeless (channel1_consumer t).
  Proof.
    apply _.
  Qed.

  Lemma channel1_producer_exclusive t :
    channel1_producer t -∗
    channel1_producer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hpending) (%_l & %_γ & %Heq & _Hmeta & Hpending')". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (oneshot_pending_valid_2 with "Hpending Hpending'") as %(? & _). done.
  Qed.

  Lemma channel1_consumer_exclusive t :
    channel1_consumer t -∗
    channel1_consumer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hexcl) (%_l & %_γ & %Heq & _Hmeta & Hexcl')". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (excl_exclusive with "Hexcl Hexcl'") as %[].
  Qed.

  Lemma channel1_create_spec P :
    {{{ True }}}
      channel1_create condition #()
    {{{ t,
      RET t;
      channel1_inv t P ∗
      channel1_producer t ∗
      channel1_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_apply (record3_make_spec with "[//]") as "%l (Hl & Hmeta)".
    iDestruct (record3_model_eq_1 with "Hl") as "(Hflag & Hmtx & Hcond)".

    iMod (oneshot_alloc ()) as "(%γ_producer & Hpending)".
    iEval (assert (1 = 2/3 + 1/3)%Qp as -> by compute_done) in "Hpending".
    iDestruct "Hpending" as "(Hpending1 & Hpending2)".

    iMod (excl_alloc (excl_G := channel1_G_consumer_G) ()) as "(%γ_consumer & Hexcl)".

    pose γ := {|
      channel1_meta_producer := γ_producer ;
      channel1_meta_consumer := γ_consumer ;
    |}.
    iMod (meta_set _ _ γ nroot with "Hmeta") as "#Hmeta"; first done.

    wp_smart_apply (mutex_create_spec _ (channel1_inv_inner l γ P) with "[Hflag Hpending2]") as "%mtx #Hmtx_inv"; first iSteps.
    wp_store.
    iMod (mapsto_persist with "Hmtx") as "Hmtx".

    wp_smart_apply (condition_create_spec _ with "[//]") as "%cond #Hcond_inv".
    wp_store.
    iMod (mapsto_persist with "Hcond") as "Hcond".

    iSteps.
  Qed.

  Lemma channel1_signal_spec t P :
    {{{
      channel1_inv t P ∗
      channel1_producer t ∗
      P
    }}}
      channel1_signal condition t
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv) & (%_l & %_γ & %Heq & _Hmeta & Hpending) & HP) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp_rec.
    wp_load.
    wp_apply (mutex_protect_spec _ (λ _, True%I) with "[$Hmtx_inv Hpending HP]") as "% _".
    { iIntros "Hmtx_locked (%b & Hflag & Hb)". destruct b.
      - iDestruct "Hb" as "(Hshot & _)".
        iDestruct (oneshot_pending_shot with "Hpending Hshot") as %[].
      - iCombine "Hpending Hb" as "Hpending".
        assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
        iMod (oneshot_update_shot with "Hpending") as "Hshot".
        iSteps.
    }
    wp_load.
    wp_apply (condition_signal_spec with "Hcond_inv").
    iSteps.
  Qed.

  Lemma channel1_wait_spec t P :
    {{{
      channel1_inv t P ∗
      channel1_consumer t
    }}}
      channel1_wait condition t
    {{{
      RET #();
      P
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv) & (%_l & %_γ & %Heq & _Hmeta & Hexcl)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp_rec.
    do 2 wp_load.
    wp_smart_apply (mutex_protect_spec _ (λ res, ⌜res = #()⌝ ∗ P)%I with "[$Hmtx_inv Hexcl]").
    { iIntros "Hmtx_locked Hsignal_inv".
      pose (Ψ b := (
        if b then
          P
        else
          excl γ.(channel1_meta_consumer) ()
      )%I).
      wp_smart_apply (condition_wait_until_spec _ Ψ with "[$Hcond_inv $Hmtx_inv $Hmtx_locked $Hsignal_inv $Hexcl]").
      { clear. iStep 15 as (Φ b) "Hb Hexcl Hflag".
        destruct b; last iSteps.
        iDestruct "Hb" as "(Hshot & [Hmodel | Hexcl'])"; first iSmash.
        iDestruct (excl_exclusive with "Hexcl Hexcl'") as %[].
      }
      iSteps.
    }
    iSteps.
  Qed.
End channel1_G.

#[global] Opaque channel1_create.
#[global] Opaque channel1_wait.
#[global] Opaque channel1_signal.

#[global] Opaque channel1_inv.
#[global] Opaque channel1_producer.
#[global] Opaque channel1_consumer.
