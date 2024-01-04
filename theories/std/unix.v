From Coq.Strings Require Export
  Ascii.

From heap_lang Require Import
  prelude.
From heap_lang.language Require Import
  diaframe.
From heap_lang.std Require Export
  base.

Parameter unix_close : val.

Parameter unix_fd_model : ∀ `{heap_GS : !heapGS Σ}, val → dfrac → list ascii → iProp Σ.

Axiom unix_fd_model_fractional : ∀ `{heap_GS : !heapGS Σ} fd chars,
  Fractional (λ q, unix_fd_model fd (DfracOwn q) chars).
#[global] Existing Instance unix_fd_model_fractional.
#[global] Instance unix_fd_model_as_fractional : ∀ `{heap_GS : !heapGS Σ} fd q chars,
  AsFractional (unix_fd_model fd (DfracOwn q) chars) (λ q, unix_fd_model fd (DfracOwn q) chars) q.
Proof.
  split; [done | apply _].
Qed.

Axiom unix_close_spec : ∀ `{heap_GS : !heapGS Σ} fd chars,
  {{{
    unix_fd_model fd (DfracOwn 1) chars
  }}}
    unix_close fd
  {{{
    RET #(); True
  }}}.
