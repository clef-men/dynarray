From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  notations
  proofmode.
From heap_lang.std Require Import
  opt
  lst.
From heap_lang.persistent Require Export
  base.

Implicit Types v t lst : val.

Definition pstack_empty :=
  &&Nil.

Definition pstack_is_empty :=
  lst_is_empty.

Definition pstack_push : val :=
  λ: "t" "v",
    &Cons "v" "t".

Definition pstack_pop : val :=
  λ: "t",
    match: "t" with
    | Nil =>
        &&None
    | Cons "v" "t'" =>
        &Some ("v", "t'")
    end.

Section heap_GS.
  Context `{heap_GS : !heapGS Σ}.

  Definition pstack_model t vs : iProp Σ :=
    lst_model t vs.

  #[global] Instance pstack_model_persistent t vs :
    Persistent (pstack_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance pstack_model_timeless t vs :
    Timeless (pstack_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma pstack_model_nil :
    ⊢ pstack_model pstack_empty [].
  Proof.
    apply lst_model_Nil.
  Qed.

  Lemma pstack_is_empty_spec t vs :
    {{{
      pstack_model t vs
    }}}
      pstack_is_empty t
    {{{
      RET #(bool_decide (vs = [])); True
    }}}.
  Proof.
    apply lst_is_empty_spec.
  Qed.

  Lemma pstack_push_spec t vs v :
    {{{
      pstack_model t vs
    }}}
      pstack_push t v
    {{{ t',
      RET t';
      pstack_model t' (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ #Hlst HΦ".
    wp_rec. wp_pures.
    iApply "HΦ".
    iApply (lst_model_Cons with "Hlst").
  Qed.

  Lemma pstack_pop_spec t vs :
    {{{
      pstack_model t vs
    }}}
      pstack_pop t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝
      | Some p =>
          ∃ v vs' t',
          ⌜vs = v :: vs' ∧ p = (v, t')%V⌝ ∗
          pstack_model t' vs'
      end
    }}}.
  Proof.
    iIntros "%Φ #Hlst HΦ".
    wp_rec.
    destruct vs as [| v vs]; wp_pures.
    - iApply (wp_lst_match_Nil with "Hlst").
      iSpecialize ("HΦ" $! None). iSmash.
    - iApply (wp_lst_match_Cons with "Hlst"); first done. iIntros "%lst' #Hlst' /=".
      iSpecialize ("HΦ" $! (Some (v, lst')%V)). iSteps. iFrame "#∗".
  Qed.
End heap_GS.

#[global] Opaque pstack_empty.
#[global] Opaque pstack_is_empty.
#[global] Opaque pstack_push.
#[global] Opaque pstack_pop.

#[global] Opaque pstack_model.
