/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtoms
import LeanTrominoes.PeriodicThreeSATThreeRouteDescriptorTargetRankBound

/-! # Port ranks of copied occurrence incidences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- A copied incidence keeps its exact global index when the implication-cycle
suffix is appended. -/
theorem occurrenceIncidence_tagged_mem_formula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (tagged : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (taggedMember : tagged ∈ (occurrenceIncidences source).zipIdx) :
    tagged ∈
      (PeriodicCNF.incidencesWithMetadata (formula source)).zipIdx := by
  have occurrenceLookup :=
    (List.mem_zipIdx_iff_getElem?).mp taggedMember
  have indexLt :
      tagged.2 < PeriodicCNF.presentationLiteralCount source := by
    have := List.snd_lt_of_mem_zipIdx taggedMember
    simpa using this
  apply (List.mem_zipIdx_iff_getElem?).mpr
  have prefixLookup :
      ((PeriodicCNF.incidencesWithMetadata (formula source)).take
        (PeriodicCNF.presentationLiteralCount source))[tagged.2]? =
          some tagged.1 := by
    rw [formula_incidencesWithMetadata_take_sourceCount]
    exact occurrenceLookup
  rw [List.getElem?_take_of_lt indexLt] at prefixLookup
  exact prefixLookup

/-- The copied occurrence is the first occurrence of its fresh positional
variable, so its variable-side route rank is exactly zero. -/
@[simp] theorem occurrenceIncidence_numericRouteDescriptor_targetPortRank
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (tagged : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (taggedMember : tagged ∈ (occurrenceIncidences source).zipIdx) :
    (tagged.1.numericRouteDescriptor
      (formula source) tagged.2).targetPortRank = 0 := by
  have incidenceLookup :=
    (List.mem_zipIdx_iff_getElem?).mp taggedMember
  have indexLt :
      tagged.2 < PeriodicCNF.presentationLiteralCount source := by
    have := List.snd_lt_of_mem_zipIdx taggedMember
    simpa using this
  have atomLookup :
      (allOccurrenceVariables source)[tagged.2]? =
        some tagged.1.literal.atom := by
    rw [← occurrenceIncidences_atoms]
    rw [List.getElem?_map, incidenceLookup]
    rfl
  have atomIndexLt :
      tagged.2 < (allOccurrenceVariables source).length :=
    (List.getElem?_eq_some_iff.mp atomLookup).1
  have atomEq :
      (allOccurrenceVariables source)[tagged.2] =
        tagged.1.literal.atom :=
    (List.getElem?_eq_some_iff.mp atomLookup).2
  have takeEq :
      (PeriodicCNF.variableOccurrences (formula source)).take tagged.2 =
        (allOccurrenceVariables source).take tagged.2 := by
    rw [← formula_variableOccurrences_take_sourceCount source]
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt indexLt)]
  have disjoint : List.Disjoint
      ((allOccurrenceVariables source).take tagged.2)
      ((allOccurrenceVariables source).drop tagged.2) :=
    List.disjoint_take_drop
      (allOccurrenceVariables_nodup source) (Nat.le_refl tagged.2)
  have atomDrop : tagged.1.literal.atom ∈
      (allOccurrenceVariables source).drop tagged.2 := by
    rw [List.drop_eq_getElem_cons atomIndexLt, atomEq]
    simp
  have atomNotTake : tagged.1.literal.atom ∉
      (allOccurrenceVariables source).take tagged.2 := by
    intro atomTake
    exact (List.disjoint_left.mp disjoint) atomTake atomDrop
  have zeroCount :
      @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq tagged.1.literal.atom
          ((PeriodicCNF.variableOccurrences
            (formula source)).take tagged.2) = 0 := by
    rw [takeEq]
    exact @List.count_eq_zero_of_not_mem
      (ThreeOccurrenceVariable Variable) instBEqOfDecidableEq
      (by infer_instance) tagged.1.literal.atom
      ((allOccurrenceVariables source).take tagged.2) atomNotTake
  simpa only [CNFIncidence.numericRouteDescriptor] using zeroCount

end PeriodicThreeSATThree
end LeanTrominoes
