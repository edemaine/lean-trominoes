/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkEndpoints
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceSemantics
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtoms

/-! # Variable occurrences in fixed cycle-link incidence blocks -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Every literal endpoint emitted by a cycle-link block is a genuine
positional source occurrence copy. -/
theorem cycleLinkIncidence_atom_mem_allOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (incidence : CNFIncidence (ThreeOccurrenceVariable Variable))
    (incidenceMember : incidence ∈ cycleLinkIncidences source) :
    incidence.literal.atom ∈ allOccurrenceVariables source := by
  unfold cycleLinkIncidences at incidenceMember
  rw [List.mem_flatMap] at incidenceMember
  obtain ⟨taggedLink, taggedLinkMember, incidenceMember⟩ := incidenceMember
  have linkMember : taggedLink.1 ∈ allCycleLinks source :=
    List.fst_mem_of_mem_zipIdx taggedLinkMember
  simp only [cycleLinkIncidenceBlock, List.mem_cons,
    List.not_mem_nil, or_false] at incidenceMember
  rcases incidenceMember with rfl | rfl
  · simpa [cycleLinkSourceIncidence] using
      allCycleLink_fst_mem_allOccurrenceVariables
        source taggedLink.1 linkMember
  · simpa [cycleLinkTargetIncidence] using
      allCycleLink_snd_mem_allOccurrenceVariables
        source taggedLink.1 linkMember

/-- The complete split-formula occurrence stream is its distinct copied
prefix followed by the two endpoint atoms of every explicit cycle link. -/
theorem formula_variableOccurrences_eq_occurrence_append_cycleLinkAtoms
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF.variableOccurrences (formula source) =
      allOccurrenceVariables source ++
        (cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom) := by
  calc
    PeriodicCNF.variableOccurrences (formula source) =
        (PeriodicCNF.incidencesWithMetadata (formula source)).map
          (fun incidence => incidence.literal.atom) :=
      (PeriodicCNF.incidencesWithMetadata_atoms _).symm
    _ = (occurrenceIncidences source ++ cycleIncidences source).map
          (fun incidence => incidence.literal.atom) := by
      rw [formula_incidencesWithMetadata_eq_occurrence_append_cycle]
    _ = (occurrenceIncidences source).map
          (fun incidence => incidence.literal.atom) ++
        (cycleIncidences source).map
          (fun incidence => incidence.literal.atom) := by
      rw [List.map_append]
    _ = allOccurrenceVariables source ++
        (cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom) := by
      rw [occurrenceIncidences_atoms,
        cycleLinkIncidences_eq_cycleIncidences]

end PeriodicThreeSATThree
end LeanTrominoes
