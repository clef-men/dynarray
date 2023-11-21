From iris.heap_lang Require Export
  notation.

From heap_lang Require Import
  prelude.
From heap_lang Require Export
  language.

Coercion val_of_option opt :=
  match opt with
  | None => NONEV
  | Some v => SOMEV v
  end.

Notation Fail := (
  #() #()
).

Notation "e .1" := (
  Fst e
) : expr_scope.
Notation "e .2" := (
  Snd e
) : expr_scope.

Notation "l .[ i ]" :=
  (l +ₗ i)%stdpp
( at level 2,
  left associativity,
  format "l .[ i ]"
) : stdpp_scope.
Notation "e .[ i ]" :=
  (e +ₗ #i)%E
( at level 2,
  left associativity
) : expr_scope.
