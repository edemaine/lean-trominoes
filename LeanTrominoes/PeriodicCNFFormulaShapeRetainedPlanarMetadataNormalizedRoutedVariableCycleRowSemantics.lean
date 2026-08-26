/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapUnique
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariablePairScanData

/-! # Normalized cycle rows of the routed-variable pair scan -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- A rank-two descriptor row selects its unique rank-zero descriptor at the
same target vertex.  Periodic normalization retains one complete three-arm
site for whichever adjacent slice contains that occurrence. -/
theorem normalizedRoutedVariablePairDescriptorRow_rankTwo
    (descriptors : List RouteDescriptor)
    (descriptorsNodup : descriptors.Nodup)
    (first selected : RouteDescriptor)
    (firstRankTwo : first.targetPortRank = 2)
    (selectedMember : selected ∈ descriptors)
    (selectedRankZero : selected.targetPortRank = 0)
    (targetEq : first.targetVertexIndex = selected.targetVertexIndex)
    (selectedUnique :
      ∀ second ∈ descriptors,
        second.targetPortRank = 0 →
        first.targetVertexIndex = second.targetVertexIndex →
        second = selected) :
    descriptors.flatMap (fun second =>
        normalizedRoutedVariablePairDescriptorBlock (first, second)) =
      (if selected.offset = ((0, 0) : Cell) then
          routedVariableFullSiteBlock else []) ++
        (if selected.offset = ((1, 0) : Cell) then
          routedVariableFullSiteBlock else []) := by
  rw [List.flatMap_eq_selected_of_unique descriptors
    (fun second =>
      normalizedRoutedVariablePairDescriptorBlock (first, second))
    selected descriptorsNodup selectedMember]
  · simp [normalizedRoutedVariablePairDescriptorBlock,
      routedVariableCurrentCyclePair, routedVariableNextCyclePair,
      firstRankTwo, selectedRankZero, targetEq]
  · intro second secondMember secondNe
    have currentFalse :
        routedVariableCurrentCyclePair (first, second) = false := by
      simp only [routedVariableCurrentCyclePair, decide_eq_false_iff_not]
      rintro ⟨_firstRankTwo, secondRankZero,
        secondTargetEq, _secondOffset⟩
      exact secondNe
        (selectedUnique second secondMember secondRankZero secondTargetEq)
    have nextFalse :
        routedVariableNextCyclePair (first, second) = false := by
      simp only [routedVariableNextCyclePair, decide_eq_false_iff_not]
      rintro ⟨_firstRankTwo, secondRankZero,
        secondTargetEq, _secondOffset⟩
      exact secondNe
        (selectedUnique second secondMember secondRankZero secondTargetEq)
    simp [normalizedRoutedVariablePairDescriptorBlock,
      currentFalse, nextFalse]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
