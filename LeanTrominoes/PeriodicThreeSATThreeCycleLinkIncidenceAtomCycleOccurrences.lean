/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAtomStream

/-! # Cycle-link incidence atoms as cycle-clause occurrences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open CycleLinkGroupedPortRanks

private theorem cycleFrom_eq_map_cycleLinksFrom'
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

private theorem cycleClauses_eq_map_cycleLinks'
    {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    cycleClauses copies =
      (cycleLinks copies).map fun link =>
        implicationClause link.1 link.2 := by
  cases copies with
  | nil => rfl
  | cons first rest =>
      exact cycleFrom_eq_map_cycleLinksFrom' first first rest

private theorem allCycleClauses_eq_map_allCycleLinks'
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    allCycleClauses source =
      (allCycleLinks source).map fun link =>
        implicationClause link.1 link.2 := by
  unfold allCycleClauses allCycleLinks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro atom _atomMember
  exact cycleClauses_eq_map_cycleLinks' _

private theorem implicationCycleOccurrences_eq_linkAtoms
    {Variable : Type*}
    (links : List (ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable)) :
    PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (links.map fun link =>
          implicationClause link.1 link.2)) =
      linkAtoms links := by
  induction links with
  | nil => rfl
  | cons link links induction =>
      change [link.1, link.2] ++
          PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk (links.map fun link =>
              implicationClause link.1 link.2)) =
        link.1 :: link.2 :: linkAtoms links
      rw [induction]
      rfl

/-- Erasing fixed cycle-link incidence metadata gives exactly the occurrence
word of the semantic implication-cycle suffix. -/
theorem cycleLinkIncidences_atoms_eq_cycleOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom) =
      PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (allCycleClauses source)) := by
  rw [cycleLinkIncidences_atoms,
    allCycleClauses_eq_map_allCycleLinks']
  exact (implicationCycleOccurrences_eq_linkAtoms
    (allCycleLinks source)).symm

end PeriodicThreeSATThree
end LeanTrominoes
