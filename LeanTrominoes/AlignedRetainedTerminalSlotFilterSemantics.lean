/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedRetainedTerminalSlotFilterCompiler

/-! # List semantics of aligned retained-terminal slot filtering -/

namespace LeanTrominoes.AlignedRetainedTerminalSlotFilter

theorem selected_append
    (firstControls secondControls : List Bool)
    (firstSlots secondSlots : List Slot)
    (firstLength : firstControls.length = firstSlots.length) :
    selected (firstControls ++ secondControls)
        (firstSlots ++ secondSlots) =
      selected firstControls firstSlots ++
        selected secondControls secondSlots := by
  unfold selected retainedPairs
  rw [List.zip_append firstLength, List.flatMap_append]

@[simp] theorem selected_replicate_false (slots : List Slot) :
    selected (List.replicate slots.length false) slots = [] := by
  induction slots with
  | nil => rfl
  | cons slot slots induction =>
      rw [List.length_cons, List.replicate_succ]
      simp only [selected, retainedPairs, List.zip_cons_cons,
        List.flatMap_cons, retainPair]
      exact induction

@[simp] theorem selected_replicate_true (slots : List Slot) :
    selected (List.replicate slots.length true) slots = slots := by
  induction slots with
  | nil => rfl
  | cons slot slots induction =>
      rw [List.length_cons, List.replicate_succ]
      simp only [selected, retainedPairs, List.zip_cons_cons,
        List.flatMap_cons, retainPair, if_true, List.singleton_append]
      exact congrArg (List.cons slot) induction

end LeanTrominoes.AlignedRetainedTerminalSlotFilter
