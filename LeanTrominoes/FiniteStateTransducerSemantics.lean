/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerData

/-! # Semantic composition laws for finite-state transducers -/

namespace LeanTrominoes.FiniteStateTransducer

/-- Scanning an append first scans the prefix, then scans the suffix from the
resulting control, and concatenates both emitted words. -/
theorem scan_append {Control Source Target : Type*}
    (transition : Control → Source → Control × List Target)
    (control : Control) (first second : List Source) :
    scan transition control (first ++ second) =
      let firstResult := scan transition control first
      let secondResult := scan transition firstResult.1 second
      (secondResult.1, firstResult.2 ++ secondResult.2) := by
  induction first generalizing control with
  | nil => rfl
  | cons symbol first induction =>
      simp only [List.cons_append, scan]
      let current := transition control symbol
      rw [induction current.1]
      simp [current, List.append_assoc]

end LeanTrominoes.FiniteStateTransducer
