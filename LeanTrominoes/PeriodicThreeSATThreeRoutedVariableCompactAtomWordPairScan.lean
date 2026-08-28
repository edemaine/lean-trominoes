/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCompactAtomWordData
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRankTwoBlockSelection
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorProjections

/-! # Target-index factorization of routed-variable compact word pairs -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicOrthocrossing.CarrierKeyWords
open PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- Compact source-atom word addressed directly by a rotated target index. -/
def routedVariableTargetSourceAtomWord (targetIndex : Nat) : List Bool :=
  [true, false, false] ++ natField targetIndex

/-- All rank-zero/one/two target-terminal equalities at one rotated target,
in descriptor presentation order. -/
def routedVariableCompactAtomWordBlockAtTarget
    (descriptors : List RouteDescriptor) (targetIndex : Nat) :
    List (List Bool) :=
  descriptors.flatMap fun route =>
    if route.targetPortRank ∈ routedVariableCompactTargetRanks ∧
        route.targetVertexIndex = targetIndex then
      [routeDescriptorTargetTerminalCompactAtomWord route,
        routedVariableTargetSourceAtomWord targetIndex,
        routeDescriptorTargetTerminalCompactAtomWord route,
        routedVariableTargetSourceAtomWord targetIndex]
    else []

theorem routedVariableCompactAtomWordPairBlock_eq
    (anchor route : RouteDescriptor) :
    routedVariableCompactAtomWordPairBlock (anchor, route) =
      if anchor.targetPortRank = 2 then
        if route.targetPortRank ∈ routedVariableCompactTargetRanks ∧
            route.targetVertexIndex = anchor.targetVertexIndex then
          [routeDescriptorTargetTerminalCompactAtomWord route,
            routedVariableTargetSourceAtomWord anchor.targetVertexIndex,
            routeDescriptorTargetTerminalCompactAtomWord route,
            routedVariableTargetSourceAtomWord anchor.targetVertexIndex]
        else []
      else [] := by
  unfold routedVariableCompactAtomWordPairBlock
    routedVariableCompactAtomWordBlock
    routedVariableTargetSourceAtomWord
    RouteDescriptorTargetAtomWords.word
  by_cases anchorRank : anchor.targetPortRank = 2
  · by_cases routeRank :
        route.targetPortRank ∈ routedVariableCompactTargetRanks
    · by_cases sameTarget :
          anchor.targetVertexIndex = route.targetVertexIndex
      · simp [anchorRank, routeRank, sameTarget]
      · have reverseTarget :
            route.targetVertexIndex ≠ anchor.targetVertexIndex :=
          Ne.symm sameTarget
        simp [anchorRank, routeRank, sameTarget, reverseTarget]
    · simp [anchorRank, routeRank]
  · simp [anchorRank]

/-- One outer descriptor row is either its complete target-index block or
empty according to the rank-two anchor test. -/
theorem routedVariableCompactAtomWordPairRow_eq
    (descriptors : List RouteDescriptor) (anchor : RouteDescriptor) :
    descriptors.flatMap (fun route =>
        routedVariableCompactAtomWordPairBlock (anchor, route)) =
      if anchor.targetPortRank = 2 then
        routedVariableCompactAtomWordBlockAtTarget descriptors
          anchor.targetVertexIndex
      else [] := by
  rw [routedVariableCompactAtomWordBlockAtTarget]
  by_cases anchorRank : anchor.targetPortRank = 2
  · rw [if_pos anchorRank]
    apply List.flatMap_congr
    intro route _routeMember
    rw [routedVariableCompactAtomWordPairBlock_eq]
    simp [anchorRank]
  · rw [if_neg anchorRank]
    apply List.flatMap_eq_nil_iff.mpr
    intro route _routeMember
    rw [routedVariableCompactAtomWordPairBlock_eq]
    simp [anchorRank]

/-- The complete split-descriptor word scan visits one target-indexed block
per copied occurrence, in increasing rotated target order. -/
theorem routedVariableCompactAtomWordPairScan_splitRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    routedVariableCompactAtomWordPairScan
        (splitRouteDescriptors source) =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (routedVariableCompactAtomWordBlockAtTarget
          (splitRouteDescriptors source)) := by
  unfold routedVariableCompactAtomWordPairScan
  change
    ((splitRouteDescriptors source).flatMap fun first =>
      (splitRouteDescriptors source).map fun second =>
        (first, second)).flatMap
          routedVariableCompactAtomWordPairBlock = _
  rw [List.flatMap_assoc]
  simp only [List.flatMap_map]
  let row := fun anchor : RouteDescriptor =>
    (splitRouteDescriptors source).flatMap fun route =>
      routedVariableCompactAtomWordPairBlock (anchor, route)
  calc
    (splitRouteDescriptors source).flatMap row =
        (occurrenceRouteDescriptors source).flatMap row ++
          (cycleLinkRouteDescriptors source).flatMap row := by
      rw [show splitRouteDescriptors source =
          occurrenceRouteDescriptors source ++
            cycleLinkRouteDescriptors source by rfl,
        List.flatMap_append]
    _ = (cycleLinkRouteDescriptors source).flatMap row := by
      have occurrenceRows :
          (occurrenceRouteDescriptors source).flatMap row = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro anchor anchorMember
        dsimp [row]
        rw [routedVariableCompactAtomWordPairRow_eq]
        have rankZero := occurrenceRouteDescriptor_targetPortRank_eq_zero
          source anchorMember
        simp [rankZero]
      rw [occurrenceRows, List.nil_append]
    _ = (cycleLinkRouteDescriptors source).flatMap (fun anchor =>
          if anchor.targetPortRank = 2 then
            routedVariableCompactAtomWordBlockAtTarget
              (splitRouteDescriptors source) anchor.targetVertexIndex
          else []) := by
      apply List.flatMap_congr
      intro anchor _anchorMember
      exact routedVariableCompactAtomWordPairRow_eq
        (splitRouteDescriptors source) anchor
    _ = (List.range
          (PeriodicCNF.presentationLiteralCount source)).flatMap
          (routedVariableCompactAtomWordBlockAtTarget
            (splitRouteDescriptors source)) :=
      cycleLinkRouteDescriptors_rankTwo_flatMap source
        (routedVariableCompactAtomWordBlockAtTarget
          (splitRouteDescriptors source))

end PeriodicThreeSATThree
end LeanTrominoes
