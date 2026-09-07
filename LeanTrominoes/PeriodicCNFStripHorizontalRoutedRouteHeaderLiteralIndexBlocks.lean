/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseBlockSemantics

/-! # Actual literal indices carried by ordered clause-frame headers -/

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderClauseFrame

open PeriodicCNF
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicPlanarOneInThreeToThreeDM

private theorem routedBlock_literalIndices (profile : ClauseProfile) :
    ∀ routed ∈ clauseRouteBlocks profile,
      routed.2.map HorizontalRoutedRouteHeader.descriptorOutputLiteralIndex =
        List.range routed.2.length := by
  cases profile <;> native_decide +revert

private theorem frameBlock_literalIndices (headers : List Header) :
    (frameBlock headers).map
        (fun frame => HorizontalRoutedRouteHeader.outputLiteralIndex frame.header) =
      headers.map HorizontalRoutedRouteHeader.outputLiteralIndex := by
  change (frameBlock headers).map
    (HorizontalRoutedRouteHeader.outputLiteralIndex ∘ Data.header) = _
  rw [← List.map_map, frameBlock_map_header]

private theorem clauseFrameBlocks_literalIndices
    (profile : ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    ∀ block ∈ clauseFrameBlocks profile prefixes,
      block.map (fun frame => HorizontalRoutedRouteHeader.outputLiteralIndex frame.header) =
        List.range block.length := by
  intro block member
  obtain ⟨headers, headersMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨routed, routedMember, rfl⟩ := List.mem_map.mp headersMember
  rw [frameBlock_literalIndices]
  have mapped : (routed.2.map (headerOf prefixes)).map
      HorizontalRoutedRouteHeader.outputLiteralIndex =
        routed.2.map HorizontalRoutedRouteHeader.descriptorOutputLiteralIndex := by
    rw [List.map_map]
    rfl
  rw [mapped, routedBlock_literalIndices profile routed routedMember]
  simp only [frameBlock, List.length_map, List.length_zipIdx]

private theorem finalFrameBlocks_literalIndices
    (profiles : List ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    ∀ block ∈ finalFrameBlocks profiles prefixes,
      block.map (fun frame => HorizontalRoutedRouteHeader.outputLiteralIndex frame.header) =
        List.range block.length := by
  induction profiles generalizing prefixes with
  | nil => simp [finalFrameBlocks]
  | cons profile profiles induction =>
      intro block member
      simp only [finalFrameBlocks, List.mem_append] at member
      rcases member with member | member
      · exact clauseFrameBlocks_literalIndices _ _ block member
      · exact induction _ block member

/-- Every retained header names its own literal position in its actual
output clause, including the two-literal complement clauses. -/
theorem outputBlock_literalIndices
    (source : List Token) (block : List Data)
    (member : block ∈ outputBlocks source) :
    block.map (fun frame => HorizontalRoutedRouteHeader.outputLiteralIndex frame.header) =
      List.range block.length := by
  obtain ⟨token, _, blockMember⟩ := List.mem_flatMap.mp member
  cases token with
  | «variable» => simp [tokenBlocks] at blockMember
  | clause profile => exact finalFrameBlocks_literalIndices _ _ block blockMember

/-- Connector kind and polarity are jointly those of the actual literal
indices, with every clause boundary retained. -/
theorem outputBlock_kind_polarity
    (source : List Token) (block : List Data)
    (member : block ∈ outputBlocks source) :
    block.map (fun frame =>
        (HorizontalRoutedRouteHeader.outputConnectorKind frame.header,
          HorizontalRoutedRouteHeader.outputPolarity frame.header)) =
      (List.range block.length).map fun index =>
        (connectorKindOfLiteralIndex index,
          PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity index) := by
  have fields := congrArg
    (List.map fun index => (connectorKindOfLiteralIndex index,
      PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity index))
    (outputBlock_literalIndices source block member)
  simpa only [List.map_map, Function.comp_def, HorizontalRoutedRouteHeader.outputConnectorKind,
    HorizontalRoutedRouteHeader.outputPolarity] using fields

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderClauseFrame
