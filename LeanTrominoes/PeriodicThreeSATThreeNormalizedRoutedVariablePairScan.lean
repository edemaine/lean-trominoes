/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRankTwoBlockSelection
import LeanTrominoes.PeriodicThreeSATThreeNormalizedRoutedVariableCycleRow

/-! # Exact normalized routed-variable pair scan of split descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Scanning every cycle descriptor row retains one complete normalized
site per rotated occurrence-copy target, in target-index order. -/
theorem splitRouteDescriptor_normalizedRoutedVariable_cycleRows
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (forward : source.IsForwardLocal)
    (zeroAnchored : source.IsZeroAnchored) :
    ((cycleLinkRouteDescriptors source).flatMap fun first =>
        (splitRouteDescriptors source).flatMap fun second =>
          normalizedRoutedVariablePairDescriptorBlock (first, second)) =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun _targetIndex => routedVariableFullSiteBlock) := by
  calc
    (cycleLinkRouteDescriptors source).flatMap (fun first =>
        (splitRouteDescriptors source).flatMap fun second =>
          normalizedRoutedVariablePairDescriptorBlock (first, second)) =
      (cycleLinkRouteDescriptors source).flatMap (fun first =>
        if first.targetPortRank = 2 then
          routedVariableFullSiteBlock
        else []) := by
          apply List.flatMap_congr
          intro first firstMember
          exact splitRouteDescriptor_normalizedRoutedVariable_cycleRow
            source forward zeroAnchored firstMember
    _ = (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun _targetIndex => routedVariableFullSiteBlock) :=
      cycleLinkRouteDescriptors_rankTwo_flatMap source
        (fun _targetIndex => routedVariableFullSiteBlock)

/-- Rank-zero copied-occurrence descriptors cannot be the first member of
a selected normalized cycle pair, so the complete occurrence-prefix rows
emit nothing. -/
theorem splitRouteDescriptor_normalizedRoutedVariable_occurrenceRows
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((occurrenceRouteDescriptors source).flatMap fun first =>
        (splitRouteDescriptors source).flatMap fun second =>
          normalizedRoutedVariablePairDescriptorBlock (first, second)) =
      [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro first firstMember
  have firstRankZero :=
    occurrenceRouteDescriptor_targetPortRank_eq_zero source firstMember
  apply List.flatMap_eq_nil_iff.mpr
  intro second _secondMember
  simp [normalizedRoutedVariablePairDescriptorBlock,
    routedVariableCurrentCyclePair, routedVariableNextCyclePair,
    firstRankZero]

/-- The complete normalized descriptor square contains one three-arm site
block per copied source occurrence and no boundary or translated copies. -/
theorem normalizedRoutedVariablePairDescriptorScan_splitRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (forward : source.IsForwardLocal)
    (zeroAnchored : source.IsZeroAnchored) :
    normalizedRoutedVariablePairDescriptorScan
        (splitRouteDescriptors source) =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun _targetIndex => routedVariableFullSiteBlock) := by
  unfold normalizedRoutedVariablePairDescriptorScan
  change
    ((splitRouteDescriptors source).flatMap fun first =>
      (splitRouteDescriptors source).map fun second =>
        (first, second)).flatMap
          normalizedRoutedVariablePairDescriptorBlock = _
  rw [List.flatMap_assoc]
  simp only [List.flatMap_map]
  let row := fun first : PeriodicOrthocrossing.RouteDescriptor =>
    (splitRouteDescriptors source).flatMap fun second =>
      normalizedRoutedVariablePairDescriptorBlock (first, second)
  calc
    (splitRouteDescriptors source).flatMap row =
      (occurrenceRouteDescriptors source ++
        cycleLinkRouteDescriptors source).flatMap row := by rfl
    _ = (occurrenceRouteDescriptors source).flatMap row ++
        (cycleLinkRouteDescriptors source).flatMap row := by
          rw [List.flatMap_append]
    _ = (List.range
          (PeriodicCNF.presentationLiteralCount source)).flatMap
            (fun _targetIndex => routedVariableFullSiteBlock) := by
          rw [splitRouteDescriptor_normalizedRoutedVariable_occurrenceRows,
            splitRouteDescriptor_normalizedRoutedVariable_cycleRows
              source forward zeroAnchored]
          simp

end PeriodicThreeSATThree
end LeanTrominoes
