From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  notations
  proofmode.
From heap_lang.std Require Export
  base.
From heap_lang.std Require Import
  diverge.

Definition assume : val :=
  λ: "b",
    if: "b" then #() else diverge #().

Section heap_GS.
  Context `{heap_GS : !heapGS Σ}.

  Lemma assume_spec (b : bool) Φ :
    ▷ (⌜b = true⌝ → Φ #()) -∗
    WP assume #b {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_rec. destruct b; first iSmash.
    wp_smart_apply wp_diverge.
  Qed.
  Lemma assume_spec' ϕ `{!Decision ϕ} Φ :
    ▷ (⌜ϕ⌝ → Φ #()) -∗
    WP assume #(bool_decide ϕ) {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_apply assume_spec. iIntros (Hϕ%bool_decide_eq_true_1).
    iSmash.
  Qed.
End heap_GS.

#[global] Opaque assume.
