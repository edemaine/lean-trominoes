/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAtoms
import LeanTrominoes.PeriodicThreeSATThreeExactFormulaVariableEnumeration

/-! # Last-occurrence order of cycle-link incidence atoms -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Erasing cycle-link incidence metadata gives exactly the variable-
occurrence stream of the implication-cycle clause suffix. -/
theorem cycleLinkIncidences_atoms_eq_cycleVariableOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom) =
      PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (allCycleClauses source)) := by
  have combined :=
    formula_variableOccurrences_eq_occurrence_append_cycleLinkAtoms source
  unfold formula at combined
  rw [variableOccurrences_append,
    occurrenceClauses_variableOccurrences] at combined
  exact (List.append_cancel_left combined).symm

/-- The cycle-link suffix mentions exactly the positional copies introduced
by the copied source prefix. -/
@[simp] theorem mem_cycleLinkIncidenceAtoms_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (copy : ThreeOccurrenceVariable Variable) :
    copy ∈ (cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom) ↔
      copy ∈ allOccurrenceVariables source := by
  constructor
  · intro copyMember
    rcases List.mem_map.mp copyMember with
      ⟨incidence, incidenceMember, rfl⟩
    exact cycleLinkIncidence_atom_mem_allOccurrenceVariables
      source incidence incidenceMember
  · intro copyMember
    rw [cycleLinkIncidences_atoms_eq_cycleVariableOccurrences]
    rw [← List.count_pos_iff]
    rw [allCycleClauses_count_eq_two_of_mem_allOccurrenceVariables
      source copy copyMember]
    omega

/-- Last-occurrence deduplication of the fixed cycle-link incidence stream
recovers the grouped one-step rotation of all occurrence copies. -/
theorem cycleLinkIncidences_atoms_dedup_eq_rotatedOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    ((cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom)).dedup =
      rotatedOccurrenceVariables source := by
  rw [cycleLinkIncidences_atoms_eq_cycleVariableOccurrences,
    allCycleClauses_variableOccurrences_dedup_eq_rotated]

end PeriodicThreeSATThree
end LeanTrominoes
