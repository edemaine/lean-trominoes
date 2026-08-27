/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteIncidenceDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteIncidenceHeaderSemantics

/-! # Direct normalization requests from assembled incidence-route data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget
open PeriodicThreeDM
open PeriodicThreeDM.NormalizationCompiler
open PeriodicThreeDM.NormalizationDirectionRequest

/-- Initial contracted direction word expressed solely through proof-free
assembled incidence routes. -/
def horizontalAssembledContractedDirections
    (source : PeriodicCNF Nat) : ContractedEdge → List AxisDirection
  | .retained color _atom incidence =>
      unitSubdivisionDirections
        (horizontalAssembledRouteAtTagComputed
          (source, ⟨incidence.tripleIndex, color⟩))
  | .through color _atom first second =>
      unitSubdivisionDirections
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨first.tripleIndex, color⟩)) ++
        unitSubdivisionDirections
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨second.tripleIndex, color⟩)).reverse

/-- Complete normalization request reconstructed from assembled incidence
routes and finite edge metadata. -/
def horizontalAssembledNormalizationRequest
    (source : PeriodicCNF Nat) (edge : ContractedEdge) :
    NormalizationDirectionRequest.Request :=
  { header := horizontalAssembledRouteRequestHeader source edge
    directions := horizontalAssembledContractedDirections source edge }

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteAssembledRequestStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

private theorem normalizationRequest_eq_of_fields
    (first second : NormalizationDirectionRequest.Request)
    (header : first.header = second.header)
    (directions : first.directions = second.directions) :
    first = second := by
  cases first
  cases second
  simp_all

/-- One exact direct normalization request uses only assembled incidence
route data. -/
theorem directSparse_ofEdge_eq_horizontalAssembled
    (symbols : List encoding.Γ) (edge : ContractedEdge)
    (edgeMember : edge ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.contractedEdges) :
    let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
      decider symbols
    NormalizationDirectionRequest.ofEdge
        (directSparseComputedNormalizationInputOfSymbols decider symbols)
        edge =
      horizontalAssembledNormalizationRequest source edge := by
  dsimp only
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  have edgeData := contractedEdge_incidence_members_of_mem
    input.problem edgeMember
  apply normalizationRequest_eq_of_fields
  · exact directSparse_ofEdge_header_eq_horizontalAssembled
      decider symbols edge edgeMember
  · cases edge with
    | retained color atom incidence =>
        have incidenceMember :
            incidence ∈ input.problem.incidences color atom := by
          simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
            ContractedEdge.atom] using edgeData.1
        exact directSparse_ofEdge_retained_directions_eq_assembled
          decider symbols color atom incidence incidenceMember
    | through color atom first second =>
        have firstMember : first ∈ input.problem.incidences color atom := by
          simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
            ContractedEdge.atom] using edgeData.1
        have secondMember : second ∈ input.problem.incidences color atom := by
          simpa [ContractedEdge.targetIncidence, ContractedEdge.color,
            ContractedEdge.atom] using edgeData.2.1
        exact directSparse_ofEdge_through_directions_eq_assembled
          decider symbols color atom first second firstMember secondMember

end PeriodicCNFStripReduction
end LeanTrominoes

end
