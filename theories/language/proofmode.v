From iris.proofmode Require Import
  spec_patterns
  reduction.
From iris.heap_lang Require Export
  proofmode.

From heap_lang Require Import
  prelude.
From heap_lang Require Export
  rules.

Tactic Notation "awp_smart_apply" open_constr(lem) :=
  wp_apply_core lem
    ltac:(fun H =>
      iApplyHyp H
    )
    ltac:(fun cont =>
      wp_pure _; []; cont ()
    );
  last iAuIntro.
Tactic Notation "awp_smart_apply" open_constr(lem) "without" constr(Hs) :=
  let Hs := words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  wp_apply_core lem
    ltac:(fun H =>
      iApply (wp_frame_wand with [SGoal $ SpecGoal GSpatial false [] Hs false]);
      [ iAccu
      | iApplyHyp H; pm_prettify
      ]
    )
    ltac:(fun cont =>
      wp_pure _; []; cont ()
    );
  last iAuIntro.
