From iris.heap_lang Require Export
  notation.

From ml Require Import
  prelude.
From ml Require Export
  language.

Coercion val_of_option opt :=
  match opt with
  | None => NONEV
  | Some v => SOMEV v
  end.

Notation Fail := (App #() #())
( only parsing
).

Notation "e .1" := (Fst e)
( at level 2,
  left associativity,
  format "e .1"
) : expr_scope.
Notation "e .2" := (Snd e)
( at level 2,
  left associativity,
  format "e .2"
) : expr_scope.

Notation "e .[0]" := (e +ₗ 0%Z)%stdpp
( at level 2,
  left associativity,
  format "e .[0]"
) : stdpp_scope.
Notation "e .[1]" := (e +ₗ 1%Z)%stdpp
( at level 2,
  left associativity,
  format "e .[1]"
) : stdpp_scope.
Notation "e .[2]" := (e +ₗ 2%Z)%stdpp
( at level 2,
  left associativity,
  format "e .[2]"
) : stdpp_scope.
Notation "e .[3]" := (e +ₗ 3%Z)%stdpp
( at level 2,
  left associativity,
  format "e .[3]"
) : stdpp_scope.
Notation "e .[0]" := (e +ₗ #0%Z)%E
( at level 2,
  left associativity,
  format "e .[0]"
) : expr_scope.
Notation "e .[1]" := (e +ₗ #1%Z)%E
( at level 2,
  left associativity,
  format "e .[1]"
) : expr_scope.
Notation "e .[2]" := (e +ₗ #2%Z)%E
( at level 2,
  left associativity,
  format "e .[2]"
) : expr_scope.
Notation "e .[3]" := (e +ₗ #3%Z)%E
( at level 2,
  left associativity,
  format "e .[3]"
) : expr_scope.
