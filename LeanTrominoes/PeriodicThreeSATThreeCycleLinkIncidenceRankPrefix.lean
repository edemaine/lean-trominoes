/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListMapIndices
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAtoms
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceIndices

/-! # Target ranks as cycle-link prefix counts -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- A cycle incidence's target rank is its one copied occurrence plus the
number of equal endpoints earlier in the cycle-link suffix. -/
theorem cycleLinkIncidence_numericRouteDescriptor_targetPortRank
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (tagged : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (taggedMember : tagged ∈ (cycleLinkIncidences source).zipIdx) :
    (tagged.1.numericRouteDescriptor (formula source)
      (PeriodicCNF.presentationLiteralCount source +
        tagged.2)).targetPortRank =
      1 + @List.count (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq tagged.1.literal.atom
        (((cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom)).take tagged.2) := by
  have incidenceMember : tagged.1 ∈ cycleLinkIncidences source :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have atomOriginal : tagged.1.literal.atom ∈
      allOccurrenceVariables source :=
    cycleLinkIncidence_atom_mem_allOccurrenceVariables
      source tagged.1 incidenceMember
  have originalsLength :
      (allOccurrenceVariables source).length =
        PeriodicCNF.presentationLiteralCount source := by
    simp [allOccurrenceVariables]
  have prefixEq :
      (PeriodicCNF.variableOccurrences (formula source)).take
          (PeriodicCNF.presentationLiteralCount source + tagged.2) =
        allOccurrenceVariables source ++
          ((cycleLinkIncidences source).map
            (fun incidence => incidence.literal.atom)).take tagged.2 := by
    rw [formula_variableOccurrences_eq_occurrence_append_cycleLinkAtoms,
      ← originalsLength, List.take_length_add_append]
  have copiedCount :
      @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq tagged.1.literal.atom
          (allOccurrenceVariables source) = 1 := by
    exact @List.count_eq_one_of_mem
      (ThreeOccurrenceVariable Variable) instBEqOfDecidableEq
      (by infer_instance) _ _
      (allOccurrenceVariables_nodup source) atomOriginal
  have countEq :
      @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq tagged.1.literal.atom
          ((PeriodicCNF.variableOccurrences (formula source)).take
            (PeriodicCNF.presentationLiteralCount source + tagged.2)) =
        1 + @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq tagged.1.literal.atom
          (((cycleLinkIncidences source).map
            (fun incidence => incidence.literal.atom)).take tagged.2) := by
    rw [prefixEq,
      @List.count_append
        (ThreeOccurrenceVariable Variable) instBEqOfDecidableEq,
      copiedCount]
  simpa only [CNFIncidence.numericRouteDescriptor] using countEq

end PeriodicThreeSATThree
end LeanTrominoes
