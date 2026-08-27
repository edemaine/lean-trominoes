/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectDrawingGridUnitsData
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteAssembledRequestData
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRasterRequestData

/-! # Direct raster requests from assembled incidence-route data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget
open PeriodicThreeDM
open PeriodicThreeDM.NormalizationCompiler
open PeriodicThreeDM.NormalizationDirectionRequest

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteAssembledRasterStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Source position selected from the head of the source incidence's
assembled route. -/
def directSparseAssembledRouteSourcePosition
    (symbols : List encoding.Γ) (edge : ContractedEdge) : Cell :=
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  (horizontalAssembledRouteAtTagComputed
    (source, edge.sourceTag)).headD (0, 0)

private theorem headD_eq_of_head?_eq_some
    {Value : Type*} {values : List Value} {value fallback : Value}
    (headEq : values.head? = some value) :
    values.headD fallback = value := by
  cases values with
  | nil => simp at headEq
  | cons head tail => simpa using headEq

/-- The head of one assembled route is its semantic triple position. -/
private theorem horizontalAssembledRouteAtIncidence_headD
    (source : PeriodicCNF Nat) (color : WireColor) (atom : Nat)
    (incidence : Incidence)
    (incidenceMember : incidence ∈
      (problem source).incidences color atom) :
    (horizontalAssembledRouteAtTagComputed
      (source, ⟨incidence.tripleIndex, color⟩)).headD (0, 0) =
      (presentation source).drawing.vertexPosition
        (problem source).incidenceGraph
        (.triple incidence.tripleIndex) := by
  have tagMember := incidenceTag_mem_of_incidence_mem
    (problem source) color atom incidenceMember
  have routeEq := normalizationIncidenceRoute_eq_horizontalAssembled
    source ⟨incidence.tripleIndex, color⟩ tagMember
  have endpoints :=
    (presentation source).toPlanarPresentation
      |>.incidenceRoute_endpoints_of_incidence
        color atom incidenceMember
  apply headD_eq_of_head?_eq_some
  rw [← routeEq]
  exact endpoints.1

/-- The assembled source-route head is the exact source vertex position in
the direct normalization input. -/
theorem directSparseAssembledRouteSourcePosition_eq
    (symbols : List encoding.Γ) (edge : ContractedEdge)
    (edgeMember : edge ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.contractedEdges) :
    directSparseAssembledRouteSourcePosition decider symbols edge =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.drawing.vertexPosition input.problem.incidenceGraph
        edge.toPeriodicEdge.source := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  have inputEq : input = normalizationInput source :=
    directSparseComputedNormalizationInputOfSymbols_eq decider symbols
  have edgeMemberSemantic :
      edge ∈ (problem source).contractedEdges := by
    rw [← normalizationInput_problem source, ← inputEq]
    exact edgeMember
  have edgeData := contractedEdge_incidence_members_of_mem
    (problem source) edgeMemberSemantic
  have semanticEq :
      directSparseAssembledRouteSourcePosition decider symbols edge =
        (normalizationInput source).drawing.vertexPosition
          (normalizationInput source).problem.incidenceGraph
          edge.toPeriodicEdge.source := by
    cases edge with
    | retained color atom incidence =>
        have incidenceMember :
            incidence ∈ (problem source).incidences color atom := by
          simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
            ContractedEdge.atom] using edgeData.1
        have position := horizontalAssembledRouteAtIncidence_headD
          source color atom incidence incidenceMember
        simpa only [directSparseAssembledRouteSourcePosition,
          source, ContractedEdge.sourceTag, ContractedEdge.toPeriodicEdge,
          normalizationInput_problem, normalizationInput_drawing] using
          position
    | through color atom first second =>
        have firstMember :
            first ∈ (problem source).incidences color atom := by
          simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
            ContractedEdge.atom] using edgeData.1
        have position := horizontalAssembledRouteAtIncidence_headD
          source color atom first firstMember
        simpa only [directSparseAssembledRouteSourcePosition,
          source, ContractedEdge.sourceTag, ContractedEdge.toPeriodicEdge,
          normalizationInput_problem, normalizationInput_drawing] using
          position
  have projectionEq := congrArg
    (fun selected : PeriodicThreeDM.NormalizationCompiler.Input =>
      selected.drawing.vertexPosition selected.problem.incidenceGraph
        edge.toPeriodicEdge.source) inputEq
  exact semanticEq.trans projectionEq.symm

/-- Compact affine metadata reconstructed from the emitted unary drawing
scale and assembled source-route head. -/
def directSparseAssembledRouteMetadata
    (symbols : List encoding.Γ) (edge : ContractedEdge) :
    RouteRasterRequest.Metadata :=
  let position := directSparseAssembledRouteSourcePosition
    decider symbols edge
  let gridSize := (directDrawingGridUnitsOfSymbols
    decider symbols).length
  { gridSize := gridSize
    horizontal := position.1.toNat
    verticalComplement := 2 * gridSize - position.2.toNat - 1
    color := edge.color }

/-- Complete compact raster request in source-scannable assembled form. -/
def directSparseAssembledRouteRasterRequest
    (symbols : List encoding.Γ) (edge : ContractedEdge) :
    RouteRasterRequest.Request :=
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  { metadata := directSparseAssembledRouteMetadata decider symbols edge
    normalization := horizontalAssembledNormalizationRequest source edge }

/-- One canonical compact request is exactly its assembled source form. -/
theorem directSparse_routeRasterRequest_ofEdge_eq_assembled
    (symbols : List encoding.Γ) (edge : ContractedEdge)
    (edgeMember : edge ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.contractedEdges) :
    RouteRasterRequest.ofEdge
        (directSparseComputedNormalizationInputOfSymbols decider symbols)
        edge =
      directSparseAssembledRouteRasterRequest decider symbols edge := by
  have positionEq := directSparseAssembledRouteSourcePosition_eq
    decider symbols edge edgeMember
  have gridEq := directDrawingGridUnitsOfSymbols_length decider symbols
  unfold RouteRasterRequest.ofEdge
    directSparseAssembledRouteRasterRequest
    directSparseAssembledRouteMetadata
  rw [positionEq, gridEq,
    directSparse_ofEdge_eq_horizontalAssembled
      decider symbols edge edgeMember]

/-- The complete compact request list is a direct map of the assembled
source form over contracted edges. -/
theorem directSparseRouteRasterRequestsOfSymbols_eq_assembled
    (symbols : List encoding.Γ) :
    RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
        decider symbols =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.contractedEdges.map
        (directSparseAssembledRouteRasterRequest decider symbols) := by
  unfold RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
  dsimp only
  apply List.map_congr_left
  intro edge edgeMember
  exact directSparse_routeRasterRequest_ofEdge_eq_assembled
    decider symbols edge edgeMember

end PeriodicCNFStripReduction
end LeanTrominoes

end
