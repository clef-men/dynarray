From iris.heap_lang Require Export
  notation.

From heap_lang Require Import
  prelude.
From heap_lang Require Export
  language.

Notation Fail := (
  #() #()
).

Notation "e .𝟙" := (
  Fst e
)(at level 2,
  left associativity,
  format "e .𝟙"
): expr_scope.
Notation "e .𝟚" := (
  Snd e
)(at level 2,
  left associativity,
  format "e .𝟚"
): expr_scope.

Notation "l .[ i ]" :=
  (l +ₗ i)%stdpp
( at level 2,
  i at level 200,
  left associativity,
  format "l .[ i ]"
) : stdpp_scope.
Notation "e1 .[ e2 ]" :=
  (e1 +ₗ e2)%E
( at level 2,
  e2 at level 200,
  left associativity
) : expr_scope.
