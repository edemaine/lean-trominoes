/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteRasterRequestDirectionBlock

/-! # Compact direction blocks for complete assembled raster-request lists -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicThreeDM

/-- Interpret a list pairing contracted edges with their compact direction
blocks as the corresponding complete raster-request token stream. -/
def horizontalAssembledRouteRasterRequestDirectionBlockListTokens
    (source : PeriodicCNF Nat)
    (metadata : ContractedEdge → RouteRasterRequest.Metadata)
    (entries : List
      (ContractedEdge × HorizontalAssembledContractedDirectionBlock)) :
    List GadgetSparseRouteRasterRequestTokens.Token :=
  entries.flatMap fun entry =>
    horizontalAssembledRouteRasterRequestDirectionBlockTokens
      (metadata entry.1)
      (horizontalAssembledRouteRequestHeader source entry.1)
      entry.2

/-- Pointwise compact direction-block classifications lift to an exact
classification of any list of genuine contracted-edge requests. -/
theorem horizontalAssembledRouteRasterRequestBlocks_directionBlocks
    (source : PeriodicCNF Nat)
    (edges : List ContractedEdge)
    (edgeMembers : ∀ edge ∈ edges,
      edge ∈ (horizontalThreeDMProblemComputed source).contractedEdges)
    (metadata : ContractedEdge → RouteRasterRequest.Metadata) :
    ∃ entries : List
        (ContractedEdge × HorizontalAssembledContractedDirectionBlock),
      entries.map Prod.fst = edges ∧
        edges.flatMap (fun edge =>
            GadgetSparseRouteRasterRequestTokens.requestBlock
              ({ metadata := metadata edge
                 normalization :=
                   horizontalAssembledNormalizationRequest source edge } :
                RouteRasterRequest.Request)) =
          horizontalAssembledRouteRasterRequestDirectionBlockListTokens
            source metadata entries := by
  induction edges with
  | nil =>
      exact ⟨[], rfl, rfl⟩
  | cons edge edges induction =>
      have edgeMember :
          edge ∈ (horizontalThreeDMProblemComputed source).contractedEdges :=
        edgeMembers edge (by simp)
      have restMembers : ∀ candidate ∈ edges,
          candidate ∈
            (horizontalThreeDMProblemComputed source).contractedEdges := by
        intro candidate candidateMember
        exact edgeMembers candidate (by simp [candidateMember])
      rcases horizontalAssembledNormalizationRequest_directionBlock_tokens
          source edge edgeMember (metadata edge) with
        ⟨block, blockTokens⟩
      rcases induction restMembers with
        ⟨entries, entriesEdges, entriesTokens⟩
      refine ⟨(edge, block) :: entries, ?_, ?_⟩
      · simp [entriesEdges]
      · unfold horizontalAssembledRouteRasterRequestDirectionBlockListTokens at entriesTokens ⊢
        simp only [List.flatMap_cons]
        rw [blockTokens, entriesTokens]

/-- The complete direct sparse raster-request stream admits one aligned list
of compact contracted direction blocks. -/
theorem directSparseRouteRasterRequestTokens_directionBlocks
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
      decider symbols
    let edges := (horizontalThreeDMProblemComputed source).contractedEdges
    ∃ entries : List
        (ContractedEdge × HorizontalAssembledContractedDirectionBlock),
      entries.map Prod.fst = edges ∧
        GadgetSparseRouteRasterRequestTokens.tokens
            (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
              decider symbols) =
          horizontalAssembledRouteRasterRequestDirectionBlockListTokens
            source (directSparseAssembledRouteMetadata decider symbols)
            entries := by
  dsimp only
  rw [directSparseRouteRasterRequestsOfSymbols_eq_assembled]
  unfold GadgetSparseRouteRasterRequestTokens.tokens
  unfold directSparseComputedNormalizationInputOfSymbols
  dsimp only
  rw [horizontalNormalizationInputComputed_problem]
  rw [List.flatMap_map]
  exact horizontalAssembledRouteRasterRequestBlocks_directionBlocks
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
    (horizontalThreeDMProblemComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
        decider symbols)).contractedEdges
    (fun _ member => member)
    (directSparseAssembledRouteMetadata decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
