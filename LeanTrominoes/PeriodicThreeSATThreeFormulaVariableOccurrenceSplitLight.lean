/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAtomCycleOccurrences
import LeanTrominoes.PeriodicThreeSATThreeOccurrences

/-! # Lightweight split of the reduced formula occurrence stream -/

namespace LeanTrominoes.PeriodicThreeSATThree

/-- The split formula presents its copied source occurrences first and its
cycle-link endpoint occurrences second. -/
theorem formula_variableOccurrences_eq_copied_append_cycleLinkAtoms
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF.variableOccurrences (formula source) =
      allOccurrenceVariables source ++
        (cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom) := by
  unfold formula
  rw [variableOccurrences_append,
    occurrenceClauses_variableOccurrences,
    cycleLinkIncidences_atoms_eq_cycleOccurrences]

end LeanTrominoes.PeriodicThreeSATThree
