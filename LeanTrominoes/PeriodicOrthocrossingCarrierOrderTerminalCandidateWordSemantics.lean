/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateNodeStreamData
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairMatchStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairSegmentMatchSemantics

/-! # Source-key words of direction-split terminal candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairFieldTags
open RouteDescriptorPairSourceKeyRecipePairs

theorem Segment.terminalDirectionalSourceKeyRecipePairBlocks_matchNode
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) :
    List.Forall₂
      (List.Forall₂ (MatchesNode (descriptorPairTokens pair)))
      (segment.terminalDirectionalSourceKeyRecipePairBlocks segmentIndex)
      (segment.terminalDirectionalCarrierNodeTemplateBlocks
        pair segmentIndex) := by
  simp only [Segment.terminalDirectionalSourceKeyRecipePairBlocks,
    Segment.terminalDirectionalCarrierNodeTemplateBlocks]
  have aligned :=
    segment.terminalSourceKeyRecipePairBlock_matchesNode pair segmentIndex
  exact List.Forall₂.cons aligned
    (List.Forall₂.cons aligned
      (List.Forall₂.cons aligned
        (List.Forall₂.cons aligned List.Forall₂.nil)))

theorem RouteShape.terminalDirectionalSourceKeyRecipePairBlocks_matchNode
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (List.Forall₂ (MatchesNode (descriptorPairTokens pair)))
      shape.terminalDirectionalSourceKeyRecipePairBlocks
      (shape.terminalDirectionalCarrierNodeTemplateBlocks pair) := by
  unfold RouteShape.terminalDirectionalSourceKeyRecipePairBlocks
    RouteShape.terminalDirectionalCarrierNodeTemplateBlocks
  induction (shape.segments .first).zipIdx with
  | nil => simp
  | cons tagged taggedSegments induction =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact
        (tagged.1.terminalDirectionalSourceKeyRecipePairBlocks_matchNode
          pair tagged.2).append induction

theorem terminalDirectionalSourceKeyRecipePairBlocks_matchNode
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (List.Forall₂ (MatchesNode (descriptorPairTokens pair)))
      terminalDirectionalSourceKeyRecipePairBlocks
      (terminalDirectionalCarrierNodeTemplateBlocks pair) := by
  unfold terminalDirectionalSourceKeyRecipePairBlocks
    terminalDirectionalCarrierNodeTemplateBlocks
  induction allRouteShapes with
  | nil => simp
  | cons shape shapes induction =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact
        (shape.terminalDirectionalSourceKeyRecipePairBlocks_matchNode
          pair).append induction

theorem Segment.componentRecipeBlock_terminalSourceKeyRecipePairBlock
    (segment : Segment) (segmentIndex : Nat) :
    componentRecipeBlock
        (segment.terminalSourceKeyRecipePairBlock segmentIndex) =
      segment.terminalSourceKeyRecipeBlock segmentIndex := by
  unfold Segment.terminalSourceKeyRecipePairBlock
    Segment.terminalSourceKeyRecipeBlock componentRecipeBlock
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro translate _translateMember
  simp [terminalSourceKeyRecipePair]

theorem Segment.componentRecipeBlocks_terminalDirectional
    (segment : Segment) (segmentIndex : Nat) :
    componentRecipeBlocks
        (segment.terminalDirectionalSourceKeyRecipePairBlocks segmentIndex) =
      segment.terminalDirectionalSourceKeyRecipeBlocks segmentIndex := by
  simp [componentRecipeBlocks,
    Segment.terminalDirectionalSourceKeyRecipePairBlocks,
    Segment.terminalDirectionalSourceKeyRecipeBlocks,
    segment.componentRecipeBlock_terminalSourceKeyRecipePairBlock]

theorem RouteShape.componentRecipeBlocks_terminalDirectional
    (shape : RouteShape) :
    componentRecipeBlocks
        shape.terminalDirectionalSourceKeyRecipePairBlocks =
      shape.terminalDirectionalSourceKeyRecipeBlocks := by
  unfold RouteShape.terminalDirectionalSourceKeyRecipePairBlocks
    RouteShape.terminalDirectionalSourceKeyRecipeBlocks
    componentRecipeBlocks
  rw [List.map_flatMap]
  induction (shape.segments .first).zipIdx with
  | nil => rfl
  | cons tagged taggedSegments induction =>
      simp only [List.flatMap_cons]
      apply congrArg₂ (fun first second => first ++ second)
      · simpa [componentRecipeBlocks] using
          tagged.1.componentRecipeBlocks_terminalDirectional tagged.2
      · exact induction

theorem componentRecipeBlocks_terminalDirectional :
    componentRecipeBlocks terminalDirectionalSourceKeyRecipePairBlocks =
      terminalDirectionalSourceKeyRecipeBlocks := by
  unfold terminalDirectionalSourceKeyRecipePairBlocks
    terminalDirectionalSourceKeyRecipeBlocks componentRecipeBlocks
  rw [List.map_flatMap]
  induction allRouteShapes with
  | nil => rfl
  | cons shape shapes induction =>
      simp only [List.flatMap_cons]
      apply congrArg₂ (fun first second => first ++ second)
      · simpa [componentRecipeBlocks] using
          shape.componentRecipeBlocks_terminalDirectional
      · exact induction

/-- Direction-split source recipe pairs are exactly the semantic padded
terminal-node candidates. -/
theorem terminalDirectionalSourceKeyRecipePairWords_eq_candidates
    (pair : RouteDescriptor × RouteDescriptor) :
    RouteDescriptorPairSourceKeyRecipePairs.words
        (descriptorPairTokens pair)
        (terminalDirectionalPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        terminalDirectionalSourceKeyRecipePairBlocks =
      (terminalDirectionalCarrierNodeCandidates pair).map
        CarrierNodeSourceKeyCandidateWords.componentPair := by
  unfold terminalDirectionalCarrierNodeCandidates
  exact words_eq_map_componentPair_candidates
    (descriptorPairTokens pair)
    (terminalDirectionalPredicates.map fun predicate =>
      predicate.evalTokens (descriptorPairTokens pair))
    terminalDirectionalSourceKeyRecipePairBlocks
    (terminalDirectionalCarrierNodeTemplateBlocks pair)
    (terminalDirectionalSourceKeyRecipePairBlocks_matchNode pair)

theorem componentWords_terminalDirectionalCandidates
    (pair : RouteDescriptor × RouteDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs
          (terminalDirectionalCarrierNodeCandidates pair)) =
      ⟨terminalDirectionalSourceKeyGuardedComponentWords
        (descriptorPairTokens pair)⟩ := by
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs
  rw [← terminalDirectionalSourceKeyRecipePairWords_eq_candidates,
    RouteDescriptorPairSourceKeyRecipePairs.componentWords_words,
    componentRecipeBlocks_terminalDirectional]
  rfl

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
