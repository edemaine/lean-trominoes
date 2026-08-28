/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRouteOccurrenceFiberSemantics
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicThreeSATThreeRouteDescriptorTargetRankBound
import LeanTrominoes.PeriodicThreeSATThreeRouteDescriptorTargetVertex
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCompactAtomWordPairScan
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableRotatedEdgeIndexDedup

/-! # Target blocks as final-site routed-variable occurrence fibers -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- At a genuine rotated occurrence atom, filtering the numeric descriptor
stream by target index and ranks zero/one/two is exactly the final-site route
occurrence fiber. -/
theorem routedVariableCompactAtomWordBlockAtTarget_eq_finalSite
    {Variable : Type} [BEq Variable] [LawfulBEq Variable]
    [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ rotatedOccurrenceVariables source) :
    routedVariableCompactAtomWordBlockAtTarget
        (PeriodicCNF.numericRouteDescriptors (formula source))
        ((rotatedOccurrenceVariables source).idxOf atom) =
      ((variableRouteOccurrencesAt
          (formula source) (atom, (1, 1))).take 3).flatMap
        (fun occurrence =>
          [routeDescriptorTargetTerminalCompactAtomWord
              (occurrence.incidence.numericRouteDescriptor
                (formula source) occurrence.edgeIndex),
            routedVariableTargetSourceAtomWord
              ((rotatedOccurrenceVariables source).idxOf atom),
            routeDescriptorTargetTerminalCompactAtomWord
              (occurrence.incidence.numericRouteDescriptor
                (formula source) occurrence.edgeIndex),
            routedVariableTargetSourceAtomWord
              ((rotatedOccurrenceVariables source).idxOf atom)]) := by
  have takeEq :
      (variableRouteOccurrencesAt
          (formula source) (atom, (1, 1))).take 3 =
        variableRouteOccurrencesAt
          (formula source) (atom, (1, 1)) :=
    (List.take_eq_self_iff _).mpr
      (variableRouteOccurrencesAt_length_le_three
        (formula source)
        (formula_occurrencesAtMostThree_decidableEq source)
        (atom, (1, 1)))
  rw [takeEq]
  unfold routedVariableCompactAtomWordBlockAtTarget
    PeriodicCNF.numericRouteDescriptors
  rw [List.flatMap_map]
  rw [variableRouteOccurrencesAt_eq_flatMap_fibers]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro taggedIncidence taggedMember
  let descriptor := taggedIncidence.1.numericRouteDescriptor
    (formula source) taggedIncidence.2
  have rankLt : descriptor.targetPortRank < 3 :=
    numericRouteDescriptor_formula_targetPortRank_lt_three
      source taggedIncidence taggedMember
  have rankMember :
      descriptor.targetPortRank ∈ routedVariableCompactTargetRanks := by
    have rankCases : descriptor.targetPortRank = 0 ∨
        descriptor.targetPortRank = 1 ∨
          descriptor.targetPortRank = 2 := by
      omega
    unfold routedVariableCompactTargetRanks
    simpa using rankCases
  have incidenceAtomMember :
      taggedIncidence.1.literal.atom ∈ rotatedOccurrenceVariables source := by
    have member := PeriodicCNF.metadataIncidence_atom_mem_dedup
      (formula source) taggedIncidence taggedMember
    rwa [formula_variableOccurrences_dedup_eq_rotatedOccurrenceVariables]
      at member
  have targetEqIff :
      descriptor.targetVertexIndex =
          (rotatedOccurrenceVariables source).idxOf atom ↔
        taggedIncidence.1.literal.atom = atom := by
    rw [numericRouteDescriptor_formula_targetVertexIndex]
    constructor
    · intro indicesEq
      exact (List.idxOf_inj incidenceAtomMember).mp indicesEq
    · intro atomEq
      rw [atomEq]
  have offsetCases := formula_incidencesWithMetadata_offsets_zero_or_one
    source positiveOffsets taggedIncidence.1
      (List.fst_mem_of_mem_zipIdx taggedMember)
  rw [translatedIncidenceOccurrencesAt_eq]
  have translateMember :
      Cell.sub (1, 1) taggedIncidence.1.edge.offset ∈
        neighborTranslations := by
    rcases offsetCases with offsetZero | offsetOne
    · rw [offsetZero]
      native_decide
    · rw [offsetOne]
      native_decide
  by_cases atomEq : taggedIncidence.1.literal.atom = atom
  · have selected :
        descriptor.targetPortRank ∈ routedVariableCompactTargetRanks ∧
          descriptor.targetVertexIndex =
            (rotatedOccurrenceVariables source).idxOf atom :=
      ⟨rankMember, targetEqIff.mpr atomEq⟩
    rw [if_pos selected, if_pos atomEq, if_pos translateMember]
    rfl
  · have rejected :
        ¬(descriptor.targetPortRank ∈ routedVariableCompactTargetRanks ∧
          descriptor.targetVertexIndex =
            (rotatedOccurrenceVariables source).idxOf atom) := by
      intro selected
      exact atomEq (targetEqIff.mp selected.2)
    rw [if_neg rejected, if_neg atomEq]
    rfl

end PeriodicThreeSATThree
end LeanTrominoes
