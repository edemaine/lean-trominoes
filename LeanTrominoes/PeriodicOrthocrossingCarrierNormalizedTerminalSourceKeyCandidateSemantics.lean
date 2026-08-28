/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipePairMatchSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairMatchSemantics

/-! # Normalized terminal source-key recipes as carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipePairs

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairAffine
open RouteDescriptorPairFieldTags

theorem terminalSourceKeyRecipePair_matchesNodeAtPeriod
    (period : Nat) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment)
    (translate : Cell) (endpoint : SegmentEnd) :
    MatchesNodeAtPeriod (descriptorPairTokens pair) period
      (terminalRecipePair
        (terminalSourceKeyRecipePair segmentIndex translate endpoint))
      (⟨CarrierNode.terminal
          ⟨⟨pair.1.edgeIndex, segmentIndex, segment.evalPair pair⟩,
            translate, endpoint⟩,
        true⟩ : Template CarrierNode) := by
  have base := terminalSourceKeyRecipePair_matchesNode
    pair segmentIndex segment (0, 0) endpoint
  simpa [MatchesNodeAtPeriod, terminalRecipePair,
    CarrierNormalizedSourceKeyRecipes.terminalRecipe,
    CarrierNodeNormalizedSourceKeys.pairAtPeriod,
    CarrierNodeNormalizedSourceKeys.nodeAtPeriod,
    terminalSourceKeyRecipePair, terminalSourceKeyRecipe,
    RouteDescriptorPairSourceKeyRecipePairs.MatchesNode] using base

theorem Segment.terminalRecipePairBlock_matchesNodeAtPeriod
    (period : Nat) (segment : Segment)
    (pair : RouteDescriptor × RouteDescriptor) (segmentIndex : Nat) :
    List.Forall₂
      (MatchesNodeAtPeriod (descriptorPairTokens pair) period)
      ((segment.terminalSourceKeyRecipePairBlock segmentIndex).map
        terminalRecipePair)
      (segment.terminalCarrierNodeTemplateBlock pair segmentIndex) := by
  unfold Segment.terminalSourceKeyRecipePairBlock
    Segment.terminalCarrierNodeTemplateBlock
  induction neighborTranslations with
  | nil => simp
  | cons translate translations induction =>
      simp only [List.flatMap_cons, List.map_append, List.map_cons,
        List.map_nil, List.cons_append]
      exact List.Forall₂.cons
        (terminalSourceKeyRecipePair_matchesNodeAtPeriod
          period pair segmentIndex segment translate .start)
        (List.Forall₂.cons
          (terminalSourceKeyRecipePair_matchesNodeAtPeriod
            period pair segmentIndex segment translate .finish)
          induction)

theorem Segment.terminalRecipePairBlocks_matchNodeAtPeriod
    (period : Nat) (segment : Segment)
    (pair : RouteDescriptor × RouteDescriptor) (segmentIndex : Nat) :
    List.Forall₂
      (List.Forall₂
        (MatchesNodeAtPeriod (descriptorPairTokens pair) period))
      ((segment.terminalSourceKeyRecipePairBlocks segmentIndex).map fun block =>
        block.map terminalRecipePair)
      (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex) := by
  simp only [Segment.terminalSourceKeyRecipePairBlocks,
    Segment.terminalCarrierNodeTemplateBlocks, List.map_cons,
    List.map_nil]
  exact List.Forall₂.cons
    (Segment.terminalRecipePairBlock_matchesNodeAtPeriod
      period segment pair segmentIndex)
    (List.Forall₂.cons
      (Segment.terminalRecipePairBlock_matchesNodeAtPeriod
        period segment pair segmentIndex)
      List.Forall₂.nil)

theorem RouteShape.terminalRecipePairBlocks_matchNodeAtPeriod
    (period : Nat) (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (List.Forall₂
        (MatchesNodeAtPeriod (descriptorPairTokens pair) period))
      (shape.terminalSourceKeyRecipePairBlocks.map fun block =>
        block.map terminalRecipePair)
      (shape.terminalCarrierNodeTemplateBlocks pair) := by
  unfold RouteShape.terminalSourceKeyRecipePairBlocks
    RouteShape.terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap]
  induction (shape.segments .first).zipIdx with
  | nil => simp
  | cons tagged taggedSegments induction =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact
        (Segment.terminalRecipePairBlocks_matchNodeAtPeriod
          period tagged.1 pair tagged.2).append induction

theorem terminalRecipePairBlocks_matchNodeAtPeriod
    (period : Nat) (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (List.Forall₂
        (MatchesNodeAtPeriod (descriptorPairTokens pair) period))
      terminalRecipePairBlocks
      (terminalCarrierNodeTemplateBlocks pair) := by
  unfold terminalRecipePairBlocks terminalSourceKeyRecipePairBlocks
    terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap]
  induction allRouteShapes with
  | nil => simp
  | cons shape shapes induction =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact (RouteShape.terminalRecipePairBlocks_matchNodeAtPeriod
        period shape pair).append induction

end CarrierNormalizedSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
