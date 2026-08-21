/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkData
import LeanTrominoes.PeriodicThreeSATThreeExactSize

/-! # Exact correspondence between cycle links and implication clauses -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

@[simp] theorem cycleLinksFrom_length
    {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    (cycleLinksFrom first current rest).length = rest.length + 1 := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest induction =>
      simp [cycleLinksFrom, induction]

@[simp] theorem cycleLinks_length
    {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    (cycleLinks copies).length = copies.length := by
  cases copies with
  | nil => rfl
  | cons first rest =>
      simp [cycleLinks]

/-- There is exactly one directed cycle link per source literal occurrence. -/
@[simp] theorem allCycleLinks_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (allCycleLinks source).length =
      PeriodicCNF.presentationLiteralCount source := by
  unfold allCycleLinks
  rw [List.length_flatMap]
  simp_rw [cycleLinks_length]
  rw [occurrenceVariables_total_length, taggedLiterals_length]

theorem cycleFrom_eq_map_cycleLinksFrom
    {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    cycleFrom first current rest =
      (cycleLinksFrom first current rest).map fun link =>
        implicationClause link.1 link.2 := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest induction =>
      simp [cycleFrom, cycleLinksFrom, induction]

theorem cycleClauses_eq_map_cycleLinks
    {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    cycleClauses copies =
      (cycleLinks copies).map fun link =>
        implicationClause link.1 link.2 := by
  cases copies with
  | nil => rfl
  | cons first rest =>
      exact cycleFrom_eq_map_cycleLinksFrom first first rest

/-- Mapping all explicit directed links to implication clauses recovers the
exact semantic cycle-clause suffix. -/
theorem allCycleClauses_eq_map_allCycleLinks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    allCycleClauses source =
      (allCycleLinks source).map fun link =>
        implicationClause link.1 link.2 := by
  unfold allCycleClauses allCycleLinks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro atom atomMember
  exact cycleClauses_eq_map_cycleLinks _

end PeriodicThreeSATThree
end LeanTrominoes
