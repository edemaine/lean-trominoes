/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapIdxOfSelfBEq
import LeanTrominoes.PeriodicCNFRoutedVariableCompactAtomWordLinkSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactAtomWordSeparation
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCanonicalNormalizedLinks
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCompactAtomWordTargetBlock
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationSemantics

/-! # Exact compact atom words of canonical routed-variable links -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicCNF PeriodicOrthocrossing PlanarThreeSAT
open PeriodicOrthocrossing.RouteDescriptorPairAffine
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNFStripReduction

local instance routedVariableCompactAtomWordFinalBlockVariableDecidableEq :
    DecidableEq PeriodicCNFStripReduction.Variable :=
  fun first second => instDecidableEqProd first second

private theorem routedVariableTargetSourceAtomWord_eq
    (source : PeriodicCNF (ThreeCNFVariable Nat))
    (atom : ThreeOccurrenceVariable (ThreeCNFVariable Nat))
    (atomMember : atom ∈ rotatedOccurrenceVariables source) :
    routedVariableTargetSourceAtomWord
        ((rotatedOccurrenceVariables source).idxOf atom) =
      directSourceFinalCompactAtomWord (formula source)
        ⟨PeriodicPlanarSATVariable.atom atom⟩ := by
  unfold routedVariableTargetSourceAtomWord
    directSourceFinalCompactAtomWord
    RetainedCompactAtomWords.word
    DirectSourceFinalIndexedAtomWords.sourceVariableWord
  simp [formula_variableOccurrences_dedup_eq_rotatedOccurrenceVariables,
    atomMember]

private theorem finalSite_member
    (source : PeriodicCNF (ThreeCNFVariable Nat))
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (atom : ThreeOccurrenceVariable (ThreeCNFVariable Nat))
    (atomMember : atom ∈ rotatedOccurrenceVariables source) :
    (atom, (1, 1)) ∈ drawingVariableRouteSites (formula source) := by
  rw [drawingVariableRouteSites_formula_eq_boundary_append_rotated
    source positiveOffsets]
  apply List.mem_append.mpr
  right
  unfold rotatedVariableRouteSiteBlocks
  apply List.mem_flatMap.mpr
  refine ⟨atom, atomMember, ?_⟩
  simp [variableRouteSiteBlock, neighborTranslations,
    neighborCoordinates, Cell.add]

/-- The affine descriptor-pair word scan of an occurrence-split formula is
exactly the repeated endpoint-word block of its canonical normalized
routed-variable links. -/
theorem routedVariableCompactAtomWordPairScan_split_eq_canonicalLinks
    (source : PeriodicCNF (ThreeCNFVariable Nat))
    (sourceLocal : source.IsLocal)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    routedVariableCompactAtomWordPairScan
        (splitRouteDescriptors source) =
      (canonicalWrappedNormalizedRoutedVariableLinks source).flatMap
        (fun link =>
          [directSourceFinalCompactAtomWord (formula source) link.first,
            directSourceFinalCompactAtomWord (formula source) link.second,
            directSourceFinalCompactAtomWord (formula source) link.first,
            directSourceFinalCompactAtomWord (formula source) link.second]) := by
  rw [routedVariableCompactAtomWordPairScan_splitRouteDescriptors]
  rw [← numericRouteDescriptors_formula_eq_splitRouteDescriptors]
  rw [← rotatedOccurrenceVariables_length source]
  rw [← List.map_idxOf_self_eq_range_beq
    (rotatedOccurrenceVariables source)
    (rotatedOccurrenceVariables_nodup source)]
  rw [List.flatMap_map]
  calc
    (rotatedOccurrenceVariables source).flatMap
        (fun atom =>
          routedVariableCompactAtomWordBlockAtTarget
            (numericRouteDescriptors (formula source))
            ((rotatedOccurrenceVariables source).idxOf atom)) =
      (rotatedOccurrenceVariables source).flatMap
        (fun atom =>
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
                  ((rotatedOccurrenceVariables source).idxOf atom)])) := by
      apply List.flatMap_congr
      intro atom atomMember
      exact routedVariableCompactAtomWordBlockAtTarget_eq_finalSite
        source positiveOffsets atom atomMember
    _ = (rotatedOccurrenceVariables source).flatMap
        (fun atom =>
          ((variableRouteOccurrencesAt
              (formula source) (atom, (1, 1))).take 3).flatMap
            (fun occurrence =>
              [routeDescriptorTargetTerminalCompactAtomWord
                  (occurrence.incidence.numericRouteDescriptor
                    (formula source) occurrence.edgeIndex),
                directSourceFinalCompactAtomWord (formula source)
                  ⟨PeriodicPlanarSATVariable.atom atom⟩,
                routeDescriptorTargetTerminalCompactAtomWord
                  (occurrence.incidence.numericRouteDescriptor
                    (formula source) occurrence.edgeIndex),
                directSourceFinalCompactAtomWord (formula source)
                  ⟨PeriodicPlanarSATVariable.atom atom⟩])) := by
      apply List.flatMap_congr
      intro atom atomMember
      apply List.flatMap_congr
      intro occurrence _occurrenceMember
      rw [routedVariableTargetSourceAtomWord_eq
        source atom atomMember]
    _ = _ := by
      unfold canonicalWrappedNormalizedRoutedVariableLinks
      rw [List.flatMap_assoc]
      apply List.flatMap_congr
      intro atom atomMember
      unfold directSourceFinalCompactAtomWord
      exact (PeriodicCNF.routedVariableLinksAt_compactAtomWords_eq_occurrences
        (formula source)
        (formula_incidenceGraph_isWellFormed source)
        (formula_incidenceGraph_isLocal sourceLocal)
        (DirectSourceFinalIndexedAtomWords.sourceVariableWord
          (formula source))
        (atom, (1, 1))
        (finalSite_member source positiveOffsets atom atomMember)).symm

end PeriodicThreeSATThree
end LeanTrominoes

end
