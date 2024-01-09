From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  notations
  diaframe.
From heap_lang.std Require Export
  mutex.

Implicit Types b : bool.
Implicit Types t cond : val.

Definition condition_create : val :=
  λ: <>,
    #().

Definition condition_wait : val :=
  λ: "t" "mtx",
    #().

Definition condition_signal : val :=
  λ: "t",
    #().

Definition condition_broadcast : val :=
  λ: "t",
    #().

#[local] Definition condition_wait_until_aux : val :=
  rec: "condition_wait_until_aux" "t" "mtx" "cond" :=
    if: "cond" #() then #() else (
      condition_wait "t" "mtx" ;;
      "condition_wait_until_aux" "t" "mtx" "cond"
    ).
Definition condition_wait_until : val :=
  λ: "t" "mtx" "cond",
    condition_wait_until_aux "t" "mtx" "cond".

Definition condition_wait_while : val :=
  λ: "t" "mtx" "cond",
    condition_wait_until "t" "mtx" (λ: <>, ~ "cond" #()).

Section mutex_G.
  Context `{mutex_G : MutexG Σ}.

  Definition condition_inv t : iProp Σ :=
    True.

  #[global] Instance condition_inv_persistent t :
    Persistent (condition_inv t).
  Proof.
    apply _.
  Qed.

  Lemma condition_create_spec :
    {{{ True }}}
      condition_create #()
    {{{ t,
      RET t;
      condition_inv t
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma condition_wait_spec t mtx P :
    {{{
      condition_inv t ∗
      mutex_inv mtx P ∗
      mutex_locked mtx ∗
      P
    }}}
      condition_wait t mtx
    {{{
      RET #();
      mutex_locked mtx ∗
      P
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma condition_signal_spec t :
    {{{
      condition_inv t
    }}}
      condition_signal t
    {{{
      RET #(); True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma condition_broadcast_spec t :
    {{{
      condition_inv t
    }}}
      condition_broadcast t
    {{{
      RET #(); True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma condition_wait_until_spec Ψ t mtx cond P :
    {{{
      condition_inv t ∗
      mutex_inv mtx P ∗
      mutex_locked mtx ∗
      P ∗
      Ψ false ∗
      {{{
        mutex_locked mtx ∗
        P ∗
        Ψ false
      }}}
        cond #()
      {{{ b,
        RET #b;
        mutex_locked mtx ∗
        P ∗
        Ψ b
      }}}
    }}}
      condition_wait_until t mtx cond
    {{{
      RET #();
      mutex_locked mtx ∗
      P ∗
      Ψ true
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hlocked & HP & HΨ & #Hcond) HΦ".
    wp_rec. wp_pures.
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply ("Hcond" with "[$]") as "%b (Hlocked & HP & HΨ)".
    destruct b; first iSteps.
    wp_smart_apply (condition_wait_spec _ _ P with "[$]") as "(Hlocked & HP)".
    wp_smart_apply ("HLöb" with "Hlocked HP HΨ HΦ").
  Qed.

  Lemma condition_wait_while_spec Ψ t mtx cond P :
    {{{
      condition_inv t ∗
      mutex_inv mtx P ∗
      mutex_locked mtx ∗
      P ∗
      Ψ true ∗
      {{{
        mutex_locked mtx ∗
        P ∗
        Ψ true
      }}}
        cond #()
      {{{ b,
        RET #b;
        mutex_locked mtx ∗
        P ∗
        Ψ b
      }}}
    }}}
      condition_wait_while t mtx cond
    {{{
      RET #();
      mutex_locked mtx ∗
      P ∗
      Ψ false
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hlocked & HP & HΨ & #Hcond) HΦ".
    wp_rec.
    wp_smart_apply (condition_wait_until_spec (λ b, Ψ (negb b)) _ _ _ P with "[$Hlocked $HP $HΨ]"); last iSteps.
    iFrame "#∗". clear. iIntros "%Φ !> (Hlocked & HP & HΨ) HΦ".
    wp_smart_apply ("Hcond" with "[$]") as "%b (Hlocked & HP & HΨ)".
    destruct b; iSteps.
  Qed.
End mutex_G.

#[global] Opaque condition_create.
#[global] Opaque condition_wait.
#[global] Opaque condition_signal.
#[global] Opaque condition_broadcast.
#[global] Opaque condition_wait_until.
#[global] Opaque condition_wait_while.

#[global] Opaque condition_inv.
