/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCycleRowSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableInactiveRowSemantics
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorOccurrenceTarget
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorPositiveRank
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorProjections
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCycleTargetBlockLookup
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorNodup
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorRankZeroUniqueness

/-! # Cycle rows of the split routed-variable scan -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- A cycle-suffix row emits its indexed cycle block exactly at target rank
two; all other cycle ranks are inactive. -/
theorem splitRouteDescriptor_cycleRow
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) {first : RouteDescriptor}
    (firstMember : first ∈ cycleLinkRouteDescriptors source) :
    (splitRouteDescriptors source).flatMap (fun second =>
        routedVariablePairDescriptorBlock (first, second)) =
      if first.targetPortRank = 2 then
        routedVariableCycleBlockAtTargetIndex source
          first.targetVertexIndex
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
    have row := routedVariablePairDescriptorRow_rankTwo
      (splitRouteDescriptors source)
      (splitRouteDescriptors_nodup source)
      first selected firstRankTwo selectedFullMember
      selectedRankZero targetEq selectedUnique
    have lookup : occurrenceRouteDescriptorAtTargetIndex source
        first.targetVertexIndex = some selected := by
      rw [targetEq]
      exact occurrenceRouteDescriptorAtTargetIndex_eq_some
        source selectedMember
    simpa [routedVariableCycleBlockAtTargetIndex, lookup] using row
  · rw [if_neg firstRankTwo]
    exact routedVariablePairDescriptorRow_eq_nil_of_rank_ne_zero_two
      (splitRouteDescriptors source) first
      (cycleLinkRouteDescriptor_targetPortRank_ne_zero
        source firstMember)
      firstRankTwo

end PeriodicThreeSATThree
end LeanTrominoes
