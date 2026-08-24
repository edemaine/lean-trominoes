/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRankTwoBlockSelection
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCycleRow

/-! # Cycle suffix of the split routed-variable scan -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Scanning every cycle descriptor row emits exactly one target-indexed
cycle block per rotated occurrence-copy vertex, in target order. -/
theorem splitRouteDescriptor_cycleRows
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((cycleLinkRouteDescriptors source).flatMap fun first =>
        (splitRouteDescriptors source).flatMap fun second =>
          routedVariablePairDescriptorBlock (first, second)) =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (routedVariableCycleBlockAtTargetIndex source) := by
  calc
    (cycleLinkRouteDescriptors source).flatMap (fun first =>
        (splitRouteDescriptors source).flatMap fun second =>
          routedVariablePairDescriptorBlock (first, second)) =
      (cycleLinkRouteDescriptors source).flatMap (fun first =>
        if first.targetPortRank = 2 then
          routedVariableCycleBlockAtTargetIndex source
            first.targetVertexIndex
        else []) := by
          apply List.flatMap_congr
          intro first firstMember
          exact splitRouteDescriptor_cycleRow source firstMember
    _ = (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (routedVariableCycleBlockAtTargetIndex source) :=
      cycleLinkRouteDescriptors_rankTwo_flatMap source
        (routedVariableCycleBlockAtTargetIndex source)

end PeriodicThreeSATThree
end LeanTrominoes
