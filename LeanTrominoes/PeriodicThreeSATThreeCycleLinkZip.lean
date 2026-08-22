/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkData

/-! # Cycle links as a one-step cyclic zip -/

namespace LeanTrominoes.PeriodicThreeSATThree

theorem cycleLinksFrom_eq_zip
    {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    cycleLinksFrom first current rest =
      List.zip (current :: rest) (rest ++ [first]) := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest induction =>
      simp [cycleLinksFrom, induction]

/-- Each copy is linked to the next copy, with the final copy linked back to
the first. -/
theorem cycleLinks_eq_zip
    {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    cycleLinks copies =
      List.zip copies (copies.tail ++ copies.take 1) := by
  cases copies with
  | nil => rfl
  | cons first rest =>
      exact cycleLinksFrom_eq_zip first first rest

end LeanTrominoes.PeriodicThreeSATThree
