/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseContractedRouteRasterSourceData
import LeanTrominoes.PeriodicCNFStripHorizontalContractedRouteRasterSourceData

/-! # Direct compact routed source entries for raster requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicThreeDM
open PeriodicThreeDM.NormalizationDirectionRequest

/-- One complete direct edge entry with its finite raster prefix retained and
its incidence geometry represented by the compact routed request language. -/
def directSparseCompactContractedRouteEntry
    (source : PeriodicCNF Nat)
    (metadata : RouteRasterRequest.Metadata)
    (edge : ContractedEdge)
    (block : HorizontalAssembledContractedDirectionBlock) :
    HorizontalContractedRouteRasterSource.Entry where
  leading := directSparseContractedRouteLeadingTokens source metadata edge
  requests := HorizontalContractedRoutedRequest.contractedInputTokens [block]

/-- If the compact block denotes the assembled direction word of an edge,
the fixed framed pipeline emits that edge's exact canonical raster request.
This packages metadata, all six header fields, contracted-role assembly, and
the outer request delimiter into one source-emitter correctness lemma. -/
theorem directSparseCompactContractedRouteEntry_output
    (source : PeriodicCNF Nat)
    (metadata : RouteRasterRequest.Metadata)
    (edge : ContractedEdge)
    (block : HorizontalAssembledContractedDirectionBlock)
    (directions : block.directions =
      horizontalAssembledContractedDirections source edge) :
    (directSparseCompactContractedRouteEntry
        source metadata edge block).output =
      GadgetSparseRouteRasterRequestTokens.requestBlock
        ({ metadata := metadata
           normalization := horizontalAssembledNormalizationRequest
             source edge } : RouteRasterRequest.Request) := by
  unfold HorizontalContractedRouteRasterSource.Entry.output
    directSparseCompactContractedRouteEntry
    directSparseContractedRouteLeadingTokens
  rw [HorizontalContractedRoutedRequest.contractedOutput_inputTokens]
  unfold HorizontalContractedRoutedRequest.contractedOutputTokens
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [PeriodicThreeDM.ContractedRouteRasterSource.rasterizeDirections_routeBlock,
    directions]
  unfold GadgetSparseRouteRasterRequestTokens.requestBlock
    GadgetSparseRouteRasterRequestTokens.requestTokens
    horizontalAssembledNormalizationRequest
    NormalizationDirectionRequest.Request.tokens
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, List.cons_append, List.nil_append, List.append_assoc]

/-- One edge paired with its compact assembled incidence block. -/
abbrev DirectSparseCompactContractedEdgeBlock :=
  ContractedEdge × HorizontalAssembledContractedDirectionBlock

/-- Framed entries obtained from an ordered list of compact edge blocks. -/
def directSparseCompactContractedRouteEntries
    (source : PeriodicCNF Nat)
    (metadata : ContractedEdge → RouteRasterRequest.Metadata)
    (blocks : List DirectSparseCompactContractedEdgeBlock) :
    List HorizontalContractedRouteRasterSource.Entry :=
  blocks.map fun tagged =>
    directSparseCompactContractedRouteEntry
      source (metadata tagged.1) tagged.1 tagged.2

/-- Canonical raster requests represented by the same ordered edge blocks. -/
def directSparseCompactContractedRouteRequests
    (source : PeriodicCNF Nat)
    (metadata : ContractedEdge → RouteRasterRequest.Metadata)
    (blocks : List DirectSparseCompactContractedEdgeBlock) :
    List RouteRasterRequest.Request :=
  blocks.map fun tagged =>
    { metadata := metadata tagged.1
      normalization := horizontalAssembledNormalizationRequest
        source tagged.1 }

/-- Pointwise direction correctness lifts to the exact edge-major compact
raster-request word. -/
theorem directSparseCompactContractedRouteEntries_outputTokens
    (source : PeriodicCNF Nat)
    (metadata : ContractedEdge → RouteRasterRequest.Metadata)
    (blocks : List DirectSparseCompactContractedEdgeBlock)
    (directions : ∀ tagged ∈ blocks,
      tagged.2.directions =
        horizontalAssembledContractedDirections source tagged.1) :
    HorizontalContractedRouteRasterSource.outputTokens
        (directSparseCompactContractedRouteEntries
          source metadata blocks) =
      GadgetSparseRouteRasterRequestTokens.tokens
        (directSparseCompactContractedRouteRequests
          source metadata blocks) := by
  unfold HorizontalContractedRouteRasterSource.outputTokens
    directSparseCompactContractedRouteEntries
    directSparseCompactContractedRouteRequests
    GadgetSparseRouteRasterRequestTokens.tokens
  rw [List.flatMap_map, List.flatMap_map]
  apply List.flatMap_congr
  intro tagged member
  exact directSparseCompactContractedRouteEntry_output
    source (metadata tagged.1) tagged.1 tagged.2
      (directions tagged member)

/-- Framing the ordered entries and running the fixed outer block map gives
the same exact edge-major compact raster-request word. -/
theorem directSparseCompactContractedRouteEntries_mappedOutput
    (source : PeriodicCNF Nat)
    (metadata : ContractedEdge → RouteRasterRequest.Metadata)
    (blocks : List DirectSparseCompactContractedEdgeBlock)
    (directions : ∀ tagged ∈ blocks,
      tagged.2.directions =
        horizontalAssembledContractedDirections source tagged.1) :
    TM2EndDelimitedBlockMap.mappedOutput
        HorizontalContractedRouteRasterSource.isEnd
        HorizontalContractedRouteRasterSource.requestOutput
        (HorizontalContractedRouteRasterSource.tokens
          (directSparseCompactContractedRouteEntries
            source metadata blocks)) =
      GadgetSparseRouteRasterRequestTokens.tokens
        (directSparseCompactContractedRouteRequests
          source metadata blocks) := by
  rw [HorizontalContractedRouteRasterSource.mappedOutput_tokens]
  exact directSparseCompactContractedRouteEntries_outputTokens
    source metadata blocks directions

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance
    directSparseCompactContractedRouteSourceDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Ordered block projection and pointwise direction correctness are the only
semantic obligations needed for a complete direct compact source word. -/
theorem directSparseCompactContractedRouteEntries_mappedOutput_of_blocks
    (symbols : List encoding.Γ)
    (blocks : List DirectSparseCompactContractedEdgeBlock)
    (edges : blocks.map Prod.fst =
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.contractedEdges)
    (directions : ∀ tagged ∈ blocks,
      tagged.2.directions =
        horizontalAssembledContractedDirections
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
            decider symbols) tagged.1) :
    TM2EndDelimitedBlockMap.mappedOutput
        HorizontalContractedRouteRasterSource.isEnd
        HorizontalContractedRouteRasterSource.requestOutput
        (HorizontalContractedRouteRasterSource.tokens
          (directSparseCompactContractedRouteEntries
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
            (directSparseAssembledRouteMetadata decider symbols)
            blocks)) =
      GadgetSparseRouteRasterRequestTokens.tokens
        (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
          decider symbols) := by
  rw [directSparseCompactContractedRouteEntries_mappedOutput
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
    (directSparseAssembledRouteMetadata decider symbols)
    blocks directions]
  apply congrArg GadgetSparseRouteRasterRequestTokens.tokens
  have edges' := edges
  unfold directSparseComputedNormalizationInputOfSymbols at edges'
  rw [horizontalNormalizationInputComputed_problem] at edges'
  rw [directSparseRouteRasterRequestsOfSymbols_eq_assembled]
  unfold directSparseComputedNormalizationInputOfSymbols
  dsimp only
  rw [horizontalNormalizationInputComputed_problem, ← edges']
  unfold directSparseCompactContractedRouteRequests
    directSparseAssembledRouteRasterRequest
  rw [List.map_map]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
