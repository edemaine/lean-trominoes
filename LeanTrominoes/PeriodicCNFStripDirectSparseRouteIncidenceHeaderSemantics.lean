/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseComputedAssignmentData
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizationInputSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMIncidenceRouteLookup
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestIncidenceHeader

/-! # Direct request headers as assembled incidence endpoint directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget
open PeriodicThreeDM
open PeriodicThreeDM.NormalizationCompiler
open PeriodicThreeDM.NormalizationDirectionRequest

/-- First-direction side/color data read from one proof-free assembled
incidence route. -/
def horizontalAssembledIncidenceSideColor
    (source : PeriodicCNF Nat) (tag : IncidenceTag) : EndpointSideColor :=
  (VertexSide.ofDirection
    (AxisDirection.polylineFirstDirection
      (horizontalAssembledRouteAtTagComputed (source, tag))),
    tag.color)

/-- Canonical RGB fan data read from three proof-free assembled routes. -/
def horizontalAssembledIncidenceColorTripleData
    (source : PeriodicCNF Nat) (tripleIndex : Nat) :
    EndpointTripleData :=
  (horizontalAssembledIncidenceSideColor source
      ⟨tripleIndex, .red⟩,
    horizontalAssembledIncidenceSideColor source
      ⟨tripleIndex, .green⟩,
    horizontalAssembledIncidenceSideColor source
      ⟨tripleIndex, .blue⟩)

/-- Canonical finite endpoint data for a triple endpoint. -/
def horizontalAssembledTripleEndpointHeaderData
    (source : PeriodicCNF Nat) (tripleIndex : Nat)
    (color : WireColor) : EndpointHeaderData :=
  { vertexIsTriple := true
    fan := some
      (horizontalAssembledIncidenceColorTripleData source tripleIndex)
    endpoint := horizontalAssembledIncidenceSideColor source
      ⟨tripleIndex, color⟩ }

/-- Terminal-direction side/color data read from one proof-free assembled
incidence route. -/
def horizontalAssembledRetainedIncidenceSideColor
    (source : PeriodicCNF Nat) (color : WireColor)
    (incidence : Incidence) : EndpointSideColor :=
  (VertexSide.ofDirection
    (AxisDirection.polylineLastDirection
      (horizontalAssembledRouteAtTagComputed
        (source, ⟨incidence.tripleIndex, color⟩))).opposite,
    color)

/-- Retained element fan data in original incidence-list order. -/
def horizontalAssembledRetainedElementTripleData
    (source : PeriodicCNF Nat) (color : WireColor)
    (atom : Nat) : EndpointTripleData :=
  match (problem source).incidences color atom with
  | [first, second, third] =>
      (horizontalAssembledRetainedIncidenceSideColor
          source color first,
        horizontalAssembledRetainedIncidenceSideColor
          source color second,
        horizontalAssembledRetainedIncidenceSideColor
          source color third)
  | _ =>
      ((.east, color), (.north, color), (.west, color))

/-- Canonical finite endpoint data for a retained element target. -/
def horizontalAssembledRetainedElementEndpointHeaderData
    (source : PeriodicCNF Nat) (color : WireColor)
    (atom : Nat) (incidence : Incidence) : EndpointHeaderData :=
  { vertexIsTriple := false
    fan := some (horizontalAssembledRetainedElementTripleData
      source color atom)
    endpoint := horizontalAssembledRetainedIncidenceSideColor
      source color incidence }

/-- Source-side canonical header data for one contracted edge. -/
def horizontalAssembledSourceEndpointHeaderData
    (source : PeriodicCNF Nat) (edge : ContractedEdge) :
    EndpointHeaderData :=
  horizontalAssembledTripleEndpointHeaderData source
    edge.sourceIncidence.tripleIndex edge.color

/-- Target-side canonical header data for one contracted edge. -/
def horizontalAssembledTargetEndpointHeaderData
    (source : PeriodicCNF Nat) : ContractedEdge → EndpointHeaderData
  | .retained color atom incidence =>
      horizontalAssembledRetainedElementEndpointHeaderData
        source color atom incidence
  | .through color _atom _first second =>
      horizontalAssembledTripleEndpointHeaderData source
        second.tripleIndex color

/-- Complete source-scannable six-field request header. -/
def horizontalAssembledRouteRequestHeader
    (source : PeriodicCNF Nat) (edge : ContractedEdge) : Header :=
  Header.ofEndpointData
    (horizontalAssembledSourceEndpointHeaderData source edge)
    (horizontalAssembledTargetEndpointHeaderData source edge)

/-- Semantic normalization incidence lookup equals the proof-free assembled
route lookup. -/
theorem normalizationIncidenceRoute_eq_horizontalAssembled
    (source : PeriodicCNF Nat) (tag : IncidenceTag)
    (tagMember : tag ∈ (problem source).incidenceTags) :
    incidenceRoute (normalizationInput source) tag =
      horizontalAssembledRouteAtTagComputed (source, tag) := by
  have computedMember :
      tag ∈ (horizontalThreeDMProblemComputed source).incidenceTags := by
    rw [horizontalThreeDMProblemComputed_eq_problem]
    exact tagMember
  rw [← horizontalNormalizationInputComputed_eq_normalizationInput]
  exact horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag
    source tag computedMember

/-- Canonical triple endpoint data agrees exactly with the assembled-route
view. -/
theorem incidenceColorEndpointHeaderData_eq_horizontalAssembled
    (source : PeriodicCNF Nat) (tripleIndex : Nat)
    (indexLt : tripleIndex < (problem source).triples.length)
    (endpoint : ContractedEndpoint)
    (vertexEq : endpoint.vertex = .triple tripleIndex) :
    incidenceColorEndpointHeaderData (normalizationInput source)
        tripleIndex endpoint =
      horizontalAssembledTripleEndpointHeaderData
        source tripleIndex endpoint.color := by
  have redMember := (problem source).tripleIncidenceTag_mem_incidenceTags
    tripleIndex indexLt .red
  have greenMember := (problem source).tripleIncidenceTag_mem_incidenceTags
    tripleIndex indexLt .green
  have blueMember := (problem source).tripleIncidenceTag_mem_incidenceTags
    tripleIndex indexLt .blue
  have endpointMember :=
    (problem source).tripleIncidenceTag_mem_incidenceTags
      tripleIndex indexLt endpoint.color
  have endpointTagEq := endpoint.incidenceTag_eq_of_vertex_triple
    tripleIndex vertexEq
  unfold incidenceColorEndpointHeaderData incidenceColorTripleData
    incidenceSideColorAt incidenceEndpointSideColor
    horizontalAssembledTripleEndpointHeaderData
    horizontalAssembledIncidenceColorTripleData
    horizontalAssembledIncidenceSideColor
  rw [endpointTagEq,
    normalizationIncidenceRoute_eq_horizontalAssembled
      source ⟨tripleIndex, .red⟩ redMember,
    normalizationIncidenceRoute_eq_horizontalAssembled
      source ⟨tripleIndex, .green⟩ greenMember,
    normalizationIncidenceRoute_eq_horizontalAssembled
      source ⟨tripleIndex, .blue⟩ blueMember,
    normalizationIncidenceRoute_eq_horizontalAssembled
      source ⟨tripleIndex, endpoint.color⟩ endpointMember]

/-- Canonical retained-element endpoint data agrees exactly with terminal
directions of the assembled incidence routes. -/
theorem retainedElementEndpointHeaderData_eq_horizontalAssembled
    (source : PeriodicCNF Nat) (color : WireColor) (atom : Nat)
    (degreeThree : (problem source).degree color atom = 3)
    (incidence : Incidence)
    (incidenceMember : incidence ∈
      (problem source).incidences color atom) :
    retainedElementEndpointHeaderData (normalizationInput source)
        color atom incidence =
      horizontalAssembledRetainedElementEndpointHeaderData
        source color atom incidence := by
  have incidenceLength :
      ((problem source).incidences color atom).length = 3 := degreeThree
  obtain ⟨first, second, third, incidencesEq⟩ :=
    exists_eq_triple_of_length_eq_three
      ((problem source).incidences color atom) incidenceLength
  have firstMember : first ∈ (problem source).incidences color atom := by
    rw [incidencesEq]
    simp
  have secondMember : second ∈ (problem source).incidences color atom := by
    rw [incidencesEq]
    simp
  have thirdMember : third ∈ (problem source).incidences color atom := by
    rw [incidencesEq]
    simp
  have firstTagMember := incidenceTag_mem_of_incidence_mem
    (problem source) color atom firstMember
  have secondTagMember := incidenceTag_mem_of_incidence_mem
    (problem source) color atom secondMember
  have thirdTagMember := incidenceTag_mem_of_incidence_mem
    (problem source) color atom thirdMember
  have incidenceTagMember := incidenceTag_mem_of_incidence_mem
    (problem source) color atom incidenceMember
  unfold retainedElementEndpointHeaderData
    retainedElementIncidenceTripleData
    retainedIncidenceEndpointSideColor
    horizontalAssembledRetainedElementEndpointHeaderData
    horizontalAssembledRetainedElementTripleData
    horizontalAssembledRetainedIncidenceSideColor
  simp only [normalizationInput_problem, incidencesEq]
  rw [normalizationIncidenceRoute_eq_horizontalAssembled
      source ⟨first.tripleIndex, color⟩ firstTagMember,
    normalizationIncidenceRoute_eq_horizontalAssembled
      source ⟨second.tripleIndex, color⟩ secondTagMember,
    normalizationIncidenceRoute_eq_horizontalAssembled
      source ⟨third.tripleIndex, color⟩ thirdTagMember,
    normalizationIncidenceRoute_eq_horizontalAssembled
      source ⟨incidence.tripleIndex, color⟩ incidenceTagMember]

/-- The finite incidence-data header of every semantic edge is the exact
proof-free assembled-route header. -/
theorem ofIncidenceDataHeader_eq_horizontalAssembled
    (source : PeriodicCNF Nat) (edge : ContractedEdge)
    (edgeMember : edge ∈ (problem source).contractedEdges) :
    Header.ofIncidenceData (normalizationInput source) edge =
      horizontalAssembledRouteRequestHeader source edge := by
  have edgeData := contractedEdge_incidence_members_of_mem
    (problem source) edgeMember
  cases edge with
  | retained color atom incidence =>
      have incidenceMember :
          incidence ∈ (problem source).incidences color atom := by
        simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
          ContractedEdge.atom] using edgeData.1
      have tripleLt := incidence_tripleIndex_lt
        (problem source) color atom incidenceMember
      have sourceEq :=
        incidenceColorEndpointHeaderData_eq_horizontalAssembled
          source incidence.tripleIndex tripleLt
          (.source (.retained color atom incidence)) rfl
      have degreeThree : (problem source).degree color atom = 3 := by
        simpa [ContractedEdge.color, ContractedEdge.atom,
          ContractedEdge.targetIsElement] using edgeData.2.2
      have targetEq :=
        retainedElementEndpointHeaderData_eq_horizontalAssembled
          source color atom degreeThree incidence incidenceMember
      unfold Header.ofIncidenceData
        horizontalAssembledRouteRequestHeader
      simp only [sourceIncidenceEndpointHeaderData,
        targetIncidenceEndpointHeaderData,
        horizontalAssembledSourceEndpointHeaderData,
        horizontalAssembledTargetEndpointHeaderData,
        ContractedEdge.sourceIncidence, ContractedEdge.color]
      rw [sourceEq, targetEq]
      rfl
  | through color atom first second =>
      have firstMember :
          first ∈ (problem source).incidences color atom := by
        simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
          ContractedEdge.atom] using edgeData.1
      have secondMember :
          second ∈ (problem source).incidences color atom := by
        simpa [ContractedEdge.targetIncidence, ContractedEdge.color,
          ContractedEdge.atom] using edgeData.2.1
      have firstLt := incidence_tripleIndex_lt
        (problem source) color atom firstMember
      have secondLt := incidence_tripleIndex_lt
        (problem source) color atom secondMember
      have sourceEq :=
        incidenceColorEndpointHeaderData_eq_horizontalAssembled
          source first.tripleIndex firstLt
          (.source (.through color atom first second)) rfl
      have targetEq :=
        incidenceColorEndpointHeaderData_eq_horizontalAssembled
          source second.tripleIndex secondLt
          (.target (.through color atom first second)) rfl
      unfold Header.ofIncidenceData
        horizontalAssembledRouteRequestHeader
      simp only [sourceIncidenceEndpointHeaderData,
        targetIncidenceEndpointHeaderData,
        horizontalAssembledSourceEndpointHeaderData,
        horizontalAssembledTargetEndpointHeaderData,
        ContractedEdge.sourceIncidence, ContractedEdge.color]
      rw [sourceEq, targetEq]
      rfl

/-- Every semantic request header is therefore reconstructed solely from
proof-free assembled incidence routes. -/
theorem ofEdge_header_eq_horizontalAssembled
    (source : PeriodicCNF Nat) (edge : ContractedEdge)
    (edgeMember : edge ∈ (problem source).contractedEdges) :
    (NormalizationDirectionRequest.ofEdge
        (normalizationInput source) edge).header =
      horizontalAssembledRouteRequestHeader source edge := by
  calc
    (NormalizationDirectionRequest.ofEdge
        (normalizationInput source) edge).header =
        Header.ofIncidenceData (normalizationInput source) edge := by
      simpa only [normalizationInput] using
        NormalizationDirectionRequest.ofEdge_header_eq_ofIncidenceData
          (presentation source) (presentation source).problemWellFormed
          (problem_degreeTwoOrThree source) edge edgeMember
    _ = horizontalAssembledRouteRequestHeader source edge :=
      ofIncidenceDataHeader_eq_horizontalAssembled
        source edge edgeMember

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteIncidenceHeaderStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct proof-free request headers use only assembled incidence routes. -/
theorem directSparse_ofEdge_header_eq_horizontalAssembled
    (symbols : List encoding.Γ)
    (edge : ContractedEdge)
    (edgeMember : edge ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.contractedEdges) :
    let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
      decider symbols
    (NormalizationDirectionRequest.ofEdge
        (directSparseComputedNormalizationInputOfSymbols decider symbols)
        edge).header =
      horizontalAssembledRouteRequestHeader source edge := by
  dsimp only
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  have inputEq :
      directSparseComputedNormalizationInputOfSymbols decider symbols =
        normalizationInput source :=
    directSparseComputedNormalizationInputOfSymbols_eq decider symbols
  have edgeMemberSemantic :
      edge ∈ (problem source).contractedEdges := by
    rw [← normalizationInput_problem source, ← inputEq]
    exact edgeMember
  rw [inputEq]
  exact ofEdge_header_eq_horizontalAssembled
    source edge edgeMemberSemantic

end PeriodicCNFStripReduction
end LeanTrominoes

end
