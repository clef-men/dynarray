From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  notations
  proofmode.
From heap_lang.std Require Export
  base.

Implicit Types t fn : val.

Record mutex `{heap_GS : !heapGS Σ} := {
  mutex_create : val ;
  mutex_lock : val ;
  mutex_unlock : val ;

  mutex_inv : val → iProp Σ → iProp Σ ;
  mutex_locked : val → iProp Σ ;

  #[global] mutex_inv_contractive t ::
    Contractive (mutex_inv t) ;

  #[global] mutex_inv_persistent t P ::
    Persistent (mutex_inv t P) ;
  #[global] mutex_locked_timeless t ::
    Timeless (mutex_locked t) ;

  mutex_locked_exclusive t :
    mutex_locked t -∗
    mutex_locked t -∗
    False ;

  mutex_create_spec P :
    {{{
      P
    }}}
      mutex_create #()
    {{{ t,
      RET t;
      mutex_inv t P
    }}} ;

  mutex_lock_spec t P :
    {{{
      mutex_inv t P
    }}}
      mutex_lock t
    {{{
      RET #();
      mutex_locked t ∗
      P
    }}} ;

  mutex_unlock_spec t P :
    {{{
      mutex_inv t P ∗
      mutex_locked t ∗
      P
    }}}
      mutex_unlock t
    {{{
      RET #(); True
    }}} ;
}.
#[global] Arguments mutex _ {_} : assert.
#[global] Arguments Build_mutex {_ _ _ _ _ _ _ _ _ _} _ _ _ _ : assert.

Section mutex.
  Context `{heap_GS : !heapGS Σ} (mutex : mutex Σ).

  #[global] Instance mutex_inv_ne t :
    NonExpansive (mutex.(mutex_inv) t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mutex_inv_proper t :
    Proper ((≡) ==> (≡)) (mutex.(mutex_inv) t).
  Proof.
    apply _.
  Qed.

  Definition mutex_protect : val :=
    λ: "t" "fn",
      mutex.(mutex_lock) "t" ;;
      let: "res" := "fn" #() in
      mutex.(mutex_unlock) "t" ;;
      "res".

  Lemma mutex_protect_spec Ψ t P fn :
    {{{
      mutex.(mutex_inv) t P ∗
      ( mutex.(mutex_locked) t -∗
        P -∗
        WP fn #() {{ v,
          mutex.(mutex_locked) t ∗
          P ∗
          Ψ v
        }}
      )
    }}}
      mutex_protect t fn
    {{{ v,
      RET v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (mutex_lock_spec with "Hinv"). iIntros "(Hlocked & HP)".
    wp_smart_apply (wp_wand with "(Hfn Hlocked HP)"). iIntros "%v (Hlocked & HP & HΨ)".
    wp_smart_apply (mutex_unlock_spec with "[$Hinv $Hlocked $HP]").
    iSteps.
  Qed.
End mutex.

#[global] Opaque mutex_protect.

Notation "mutex .(mutex_protect)" := (
  mutex_protect mutex
)(at level 5
).
