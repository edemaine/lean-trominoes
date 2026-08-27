/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteRasterRequestDirectionBlockList
import LeanTrominoes.PeriodicThreeDMContractedRouteRasterSourceData

/-! # Direct framed source words for compact raster requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget
open PeriodicThreeDM
open PeriodicThreeDM.NormalizationDirectionRequest
open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The metadata, six finite header fields, and initial direction separator
that precede one role-assembled contracted direction word. -/
def directSparseContractedRouteLeadingTokens
    (source : PeriodicCNF Nat)
    (metadata : RouteRasterRequest.Metadata)
    (edge : ContractedEdge) :
    List PeriodicThreeDM.ContractedRouteRasterSource.RasterToken :=
  GadgetSparseRouteRasterRequestTokens.metadataTokens metadata ++
    ((horizontalAssembledRouteRequestHeader source edge).tokens ++
      [PeriodicThreeDM.NormalizationDirectionRequest.Token.separator]).map
        GadgetSparseRouteRasterRequestTokens.Token.normalization

/-- Proof-free forward incidence words for one retained or through edge. -/
def horizontalAssembledContractedEdgeBlock
    (source : PeriodicCNF Nat) : ContractedEdge →
      PeriodicThreeDM.ContractedDirectionAssembler.EdgeBlock
  | .retained color _atom incidence =>
      .retained (unitSubdivisionDirections
        (horizontalAssembledRouteAtTagComputed
          (source, ⟨incidence.tripleIndex, color⟩)))
  | .through color _atom first second =>
      .through
        (unitSubdivisionDirections
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨first.tripleIndex, color⟩)))
        (unitSubdivisionDirections
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨second.tripleIndex, color⟩)))

/-- Interpreting those two forward words performs exactly the semantic
contracted join. -/
theorem horizontalAssembledContractedEdgeBlock_directions
    (source : PeriodicCNF Nat) (edge : ContractedEdge)
    (edgeMember : edge ∈
      (horizontalThreeDMProblemComputed source).contractedEdges) :
    (horizontalAssembledContractedEdgeBlock source edge).directions =
      horizontalAssembledContractedDirections source edge := by
  cases edge with
  | retained color atom incidence => rfl
  | through color atom first second =>
      have edgeData := contractedEdge_incidence_members_of_mem
        (horizontalThreeDMProblemComputed source) edgeMember
      have secondMember : second ∈
          (horizontalThreeDMProblemComputed source).incidences color atom := by
        simpa [ContractedEdge.targetIncidence, ContractedEdge.color,
          ContractedEdge.atom] using edgeData.2.1
      have secondTagMember := incidenceTag_mem_of_incidence_mem
        (horizontalThreeDMProblemComputed source) color atom secondMember
      have width := horizontalSemanticNormalizedRibbonSource_widthAtMostThree
        source
      have compatible :=
        horizontalSemanticNormalizedRibbonSource_fansCompatible source
      have secondOrthogonal : PeriodicOrthocrossing.OrthogonalPolyline
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨second.tripleIndex, color⟩)) := by
        rw [horizontalAssembledRouteAtTagComputed_eq_semantic
          source width compatible]
        exact assembledRouteAtTag_orthogonal
          (coordinatedSourceRibbonThreeStrandRouting
            (horizontalSemanticNormalizedRibbonReadyPresentation source)
            width compatible)
          ⟨second.tripleIndex, color⟩
      change unitSubdivisionDirections
            (horizontalAssembledRouteAtTagComputed
              (source, ⟨first.tripleIndex, color⟩)) ++
          reverseDirections
            (unitSubdivisionDirections
              (horizontalAssembledRouteAtTagComputed
                (source, ⟨second.tripleIndex, color⟩))) =
        unitSubdivisionDirections
            (horizontalAssembledRouteAtTagComputed
              (source, ⟨first.tripleIndex, color⟩)) ++
          unitSubdivisionDirections
            (horizontalAssembledRouteAtTagComputed
              (source, ⟨second.tripleIndex, color⟩)).reverse
      rw [unitSubdivisionDirections_reverse _ secondOrthogonal]

def directSparseContractedRouteEntry
    (source : PeriodicCNF Nat)
    (metadata : ContractedEdge → RouteRasterRequest.Metadata)
    (edge : ContractedEdge) :
    PeriodicThreeDM.ContractedRouteRasterSource.Entry where
  leading := directSparseContractedRouteLeadingTokens
    source (metadata edge) edge
  edge := horizontalAssembledContractedEdgeBlock source edge

/-- One framed entry compiles to the exact assembled compact request block. -/
theorem directSparseContractedRouteEntry_output
    (source : PeriodicCNF Nat)
    (metadata : ContractedEdge → RouteRasterRequest.Metadata)
    (edge : ContractedEdge)
    (edgeMember : edge ∈
      (horizontalThreeDMProblemComputed source).contractedEdges) :
    (directSparseContractedRouteEntry source metadata edge).output =
      GadgetSparseRouteRasterRequestTokens.requestBlock
        ({ metadata := metadata edge
           normalization := horizontalAssembledNormalizationRequest
             source edge } : RouteRasterRequest.Request) := by
  unfold PeriodicThreeDM.ContractedRouteRasterSource.Entry.output
    directSparseContractedRouteEntry
    directSparseContractedRouteLeadingTokens
  unfold PeriodicThreeDM.ContractedDirectionAssembler.outputTokens
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [PeriodicThreeDM.ContractedRouteRasterSource.rasterizeDirections_routeBlock,
    horizontalAssembledContractedEdgeBlock_directions
      source edge edgeMember]
  unfold GadgetSparseRouteRasterRequestTokens.requestBlock
    GadgetSparseRouteRasterRequestTokens.requestTokens
    horizontalAssembledNormalizationRequest
    NormalizationDirectionRequest.Request.tokens
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, List.cons_append, List.nil_append, List.append_assoc]

def directSparseContractedRouteEntries
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    List PeriodicThreeDM.ContractedRouteRasterSource.Entry :=
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  (horizontalThreeDMProblemComputed source).contractedEdges.map
    (directSparseContractedRouteEntry source
      (directSparseAssembledRouteMetadata decider symbols))

/-- Exact finite source-emitter target after all dynamic contracted assembly
has been factored into the fixed generic compiler. -/
def directSparseContractedRouteSourceTokens
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    List PeriodicThreeDM.ContractedRouteRasterSource.Token :=
  PeriodicThreeDM.ContractedRouteRasterSource.tokens
    (directSparseContractedRouteEntries decider symbols)

/-- Running the fixed framed pipeline on its direct source target returns the
canonical compact raster-request stream. -/
theorem directSparseContractedRouteSourceTokens_output
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    TM2EndDelimitedBlockMap.mappedOutput
        PeriodicThreeDM.ContractedRouteRasterSource.isEnd
        PeriodicThreeDM.ContractedRouteRasterSource.requestOutput
        (directSparseContractedRouteSourceTokens decider symbols) =
      GadgetSparseRouteRasterRequestTokens.tokens
        (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
          decider symbols) := by
  unfold directSparseContractedRouteSourceTokens
  rw [PeriodicThreeDM.ContractedRouteRasterSource.mappedOutput_tokens]
  unfold directSparseContractedRouteEntries
    PeriodicThreeDM.ContractedRouteRasterSource.outputTokens
  dsimp only
  rw [List.flatMap_map]
  rw [directSparseRouteRasterRequestsOfSymbols_eq_assembled]
  unfold GadgetSparseRouteRasterRequestTokens.tokens
  unfold directSparseComputedNormalizationInputOfSymbols
  dsimp only
  rw [horizontalNormalizationInputComputed_problem]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro edge edgeMember
  exact directSparseContractedRouteEntry_output
    _ _ edge edgeMember

end PeriodicCNFStripReduction
end LeanTrominoes

end
