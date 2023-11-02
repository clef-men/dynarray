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

Notation "l .[0]" :=
  (l +ₗ 0)%stdpp
( at level 2,
  left associativity
) : stdpp_scope.
Notation "l .[1]" :=
  (l +ₗ 1)%stdpp
( at level 2,
  left associativity
) : stdpp_scope.
Notation "l .[2]" :=
  (l +ₗ 2)%stdpp
( at level 2,
  left associativity
) : stdpp_scope.
Notation "l .[3]" :=
  (l +ₗ 3)%stdpp
( at level 2,
  left associativity
) : stdpp_scope.
Notation "e .[0]" :=
  (e +ₗ #0)%E
( at level 2,
  left associativity
) : expr_scope.
Notation "e .[1]" :=
  (e +ₗ #1)%E
( at level 2,
  left associativity
) : expr_scope.
Notation "e .[2]" :=
  (e +ₗ #2)%E
( at level 2,
  left associativity
) : expr_scope.
Notation "e .[3]" :=
  (e +ₗ #3)%E
( at level 2,
  left associativity
) : expr_scope.
