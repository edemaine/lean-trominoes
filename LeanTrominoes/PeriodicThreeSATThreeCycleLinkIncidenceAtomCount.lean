/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleExactOccurrences
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAtomCycleOccurrences

/-! # Cycle-link incidence atom counts -/

namespace LeanTrominoes.PeriodicThreeSATThree

/-- Every copied source occurrence occurs twice among the cycle-link
incidence atoms. -/
theorem cycleLinkIncidenceAtoms_count_eq_two_of_mem_allOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ allOccurrenceVariables source) :
    ((cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom)).count atom = 2 := by
  rw [cycleLinkIncidences_atoms_eq_cycleOccurrences]
  exact allCycleClauses_count_eq_two_of_mem_allOccurrenceVariables
    source atom atomMember

end LeanTrominoes.PeriodicThreeSATThree
