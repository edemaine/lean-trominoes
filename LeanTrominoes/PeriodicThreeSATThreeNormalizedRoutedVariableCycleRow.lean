/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariableCycleRowSemantics
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorOccurrenceTarget
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorPositiveOffsets
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorProjections
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorNodup
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorRankZeroUniqueness

/-! # Normalized cycle rows of the split routed-variable scan -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- A cycle-suffix row emits one normalized complete site exactly at target
rank two; all other cycle ranks are inactive. -/
theorem splitRouteDescriptor_normalizedRoutedVariable_cycleRow
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (forward : source.IsForwardLocal)
    (zeroAnchored : source.IsZeroAnchored)
    {first : RouteDescriptor}
    (firstMember : first ∈ cycleLinkRouteDescriptors source) :
    (splitRouteDescriptors source).flatMap (fun second =>
        normalizedRoutedVariablePairDescriptorBlock (first, second)) =
      if first.targetPortRank = 2 then
        routedVariableFullSiteBlock
      else [] := by
  by_cases firstRankTwo : first.targetPortRank = 2
  · rw [if_pos firstRankTwo]
    rcases exists_occurrenceRouteDescriptor_for_cycleTarget
        source firstMember with
      ⟨selected, selectedMember, targetEq⟩
    have selectedRankZero :=
      occurrenceRouteDescriptor_targetPortRank_eq_zero
        source selectedMember
    have selectedFullMember : selected ∈
        splitRouteDescriptors source := by
      unfold splitRouteDescriptors
      exact List.mem_append_left _ selectedMember
    have selectedUnique : ∀ second ∈ splitRouteDescriptors source,
        second.targetPortRank = 0 →
        first.targetVertexIndex = second.targetVertexIndex →
        second = selected := by
      intro second secondMember secondRankZero secondTarget
      apply splitRouteDescriptor_rankZero_eq_occurrence
        source selectedMember secondMember secondRankZero
      exact targetEq.symm.trans secondTarget
    have row := normalizedRoutedVariablePairDescriptorRow_rankTwo
      (splitRouteDescriptors source)
      (splitRouteDescriptors_nodup source)
      first selected firstRankTwo selectedFullMember
      selectedRankZero targetEq selectedUnique
    rcases occurrenceRouteDescriptors_offset_zero_or_one
        source forward zeroAnchored selected selectedMember with
      selectedOffset | selectedOffset
    · simpa [selectedOffset] using row
    · simpa [selectedOffset] using row
  · rw [if_neg firstRankTwo]
    apply List.flatMap_eq_nil_iff.mpr
    intro second _secondMember
    simp [normalizedRoutedVariablePairDescriptorBlock,
      routedVariableCurrentCyclePair, routedVariableNextCyclePair,
      firstRankTwo]

end PeriodicThreeSATThree
end LeanTrominoes
