/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkAtomData

/-! # Structural semantics of cycle endpoint words -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

theorem linkAtoms_cycleLinksFrom
    {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    linkAtoms (cycleLinksFrom first current rest) =
      current :: (rest.flatMap fun value => [value, value]) ++ [first] := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest induction =>
      simp [linkAtoms, cycleLinksFrom, induction]

theorem cycleLinkAtoms_cons
    {Variable : Type*}
    (first : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    cycleLinkAtoms (first :: rest) =
      first :: (rest.flatMap fun value => [value, value]) ++ [first] := by
  exact linkAtoms_cycleLinksFrom first first rest

theorem linkAtoms_append
    {Value : Type*} (first second : List (Value × Value)) :
    linkAtoms (first ++ second) =
      linkAtoms first ++ linkAtoms second := by
  induction first with
  | nil => rfl
  | cons link first induction =>
      simp only [List.cons_append, linkAtoms]
      rw [induction]

/-- Endpoint extraction distributes over a list of occurrence cycles. -/
theorem linkAtoms_flatMap_cycleLinks
    {Variable : Type*}
    (groups : List (List (ThreeOccurrenceVariable Variable))) :
    linkAtoms (groups.flatMap cycleLinks) =
      groups.flatMap cycleLinkAtoms := by
  induction groups with
  | nil => rfl
  | cons group groups induction =>
      simp only [List.flatMap_cons, linkAtoms_append, cycleLinkAtoms]
      change linkAtoms (List.flatMap cycleLinks groups) =
        List.flatMap cycleLinkAtoms groups at induction
      rw [induction]

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
