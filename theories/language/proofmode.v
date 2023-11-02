From iris.proofmode Require Import
  spec_patterns.
From iris.heap_lang Require Export
  proofmode.

From diaframe.heap_lang Require Export
  proof_automation.

From heap_lang Require Export
  language.
From heap_lang.iris Require Export
  proofmode.
From heap_lang.iris Require Import
  program_logic.atomic.

Tactic Notation "awp_smart_apply" open_constr(lem) :=
  wp_apply_core lem
    ltac:(fun H => iApplyHyp H)
    ltac:(fun cont => wp_pure _; []; cont ());
    last iAuIntro.
Tactic Notation "awp_smart_apply" open_constr(lem) "without" constr(Hs) :=
  let Hs := words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  wp_apply_core lem
    ltac:(fun H =>
      iApply (wp_frame_wand with [SGoal $ SpecGoal GSpatial false [] Hs false]);
        [iAccu | iApplyHyp H]
    )
    ltac:(fun cont => fail);
    last iAuIntro.
