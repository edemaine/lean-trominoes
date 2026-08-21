/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRenaming

/-! # Occurrence-cycle clauses under injective atom renaming -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- One implication clause commutes with occurrence-copy renaming. -/
theorem implicationClause_rename
    {Source Target : Type*} (variableMap : Source → Target)
    (first second : ThreeOccurrenceVariable Source) :
    implicationClause (renameOccurrence variableMap first)
        (renameOccurrence variableMap second) =
      PeriodicCNF.renameClause (renameOccurrence variableMap)
        (implicationClause first second) := by
  rfl

/-- A directed cycle suffix commutes with pointwise occurrence renaming. -/
theorem cycleFrom_rename
    {Source Target : Type*} (variableMap : Source → Target)
    (first current : ThreeOccurrenceVariable Source)
    (rest : List (ThreeOccurrenceVariable Source)) :
    cycleFrom (renameOccurrence variableMap first)
        (renameOccurrence variableMap current)
        (rest.map (renameOccurrence variableMap)) =
      (cycleFrom first current rest).map
        (PeriodicCNF.renameClause (renameOccurrence variableMap)) := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest induction =>
      simp only [List.map_cons, cycleFrom, List.map_cons]
      rw [induction, implicationClause_rename]

/-- A complete directed occurrence cycle commutes with pointwise renaming. -/
theorem cycleClauses_rename
    {Source Target : Type*} (variableMap : Source → Target)
    (copies : List (ThreeOccurrenceVariable Source)) :
    cycleClauses (copies.map (renameOccurrence variableMap)) =
      (cycleClauses copies).map
        (PeriodicCNF.renameClause (renameOccurrence variableMap)) := by
  cases copies with
  | nil => rfl
  | cons first rest =>
      simp only [List.map_cons, cycleClauses]
      exact cycleFrom_rename variableMap first first rest

/-- The complete grouped implication-cycle suffix commutes with an injective
source-atom rename. -/
theorem allCycleClauses_rename_of_injective
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (source : PeriodicCNF Source) :
    allCycleClauses (source.rename variableMap) =
      (allCycleClauses source).map
        (PeriodicCNF.renameClause (renameOccurrence variableMap)) := by
  unfold allCycleClauses
  rw [sourceVariables_rename_of_injective
    variableMap injective source]
  rw [List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro atom atomMember
  rw [occurrenceVariables_rename_of_injective
    variableMap injective source atom]
  exact cycleClauses_rename variableMap
    (occurrenceVariables source atom)

end PeriodicThreeSATThree
end LeanTrominoes
