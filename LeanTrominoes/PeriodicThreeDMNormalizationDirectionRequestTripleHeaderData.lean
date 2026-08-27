/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestHeaderPermutation
import LeanTrominoes.PeriodicThreeDMNormalizationTripleColorData

/-! # Canonical RGB data for triple-endpoint request headers -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open Gadget
open NormalizationCompiler

/-- Canonical finite header data at a triple endpoint, expressed through the
first directions of the red, green, and blue original incidence routes. -/
def incidenceColorEndpointHeaderData
    (input : NormalizationCompiler.Input) (tripleIndex : Nat)
    (endpoint : ContractedEndpoint) : EndpointHeaderData :=
  { vertexIsTriple := true
    fan := some (incidenceColorTripleData input tripleIndex)
    endpoint := incidenceEndpointSideColor input endpoint }

/-- All request choices at a genuine triple endpoint can be read from the
three original incidence routes in fixed RGB order. -/
theorem tripleEndpointHeaderChoices_eq_incidenceColorData
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length)
    (endpoint : ContractedEndpoint)
    (endpointMember : endpoint ∈ problem.contractedEndpoints)
    (vertexEq : endpoint.vertex = .triple tripleIndex) :
    let input := inputOfPresentation presentation.toPlanarPresentation
    let actual := endpointHeaderData input endpoint
    let canonical :=
      incidenceColorEndpointHeaderData input tripleIndex endpoint
    actual.firstChoice = canonical.firstChoice ∧
      actual.secondChoice = canonical.secondChoice ∧
      actual.finalChoice = canonical.finalChoice := by
  dsimp only
  obtain ⟨fan⟩ := exists_contractVertexFan_at_triple
    presentation wellFormed degree tripleIndex indexLt
  let input := inputOfPresentation presentation.toPlanarPresentation
  let endpoints : EndpointTriple :=
    (fan.first, fan.second, fan.third)
  let actualData := incidenceEndpointTripleData input endpoints
  let canonicalData := incidenceColorTripleData input tripleIndex
  have compressedEq :
      endpointTripleData (input, endpoints) = actualData := by
    exact compilerEndpointTripleData_eq_incidenceTags
      presentation.toPlanarPresentation tripleIndex
      fan.first fan.second fan.third fan.endpoints_eq
  have dataAtEq :
      endpointTripleDataAt (input, .triple tripleIndex) =
        some actualData := by
    unfold endpointTripleDataAt endpointTripleAt
    dsimp [input]
    simp only [inputOfPresentation]
    rw [fan.endpoints_eq]
    simpa [input, endpoints, inputOfPresentation] using
      congrArg some compressedEq
  have firstTag :=
    fan.first.incidenceTag_eq_of_vertex_triple
      tripleIndex fan.first_data.2
  have secondTag :=
    fan.second.incidenceTag_eq_of_vertex_triple
      tripleIndex fan.second_data.2
  have thirdTag :=
    fan.third.incidenceTag_eq_of_vertex_triple
      tripleIndex fan.third_data.2
  have colorsPerm :=
    contractedVertexFan_colors_perm_incidenceColors
      degree tripleIndex fan
  have dataPerm :
      List.Perm (endpointTripleDataList actualData)
        (endpointTripleDataList canonicalData) := by
    have mapped := colorsPerm.map
      (incidenceSideColorAt input tripleIndex)
    simpa [actualData, canonicalData, endpoints,
      endpointTripleDataList, incidenceEndpointTripleData,
      incidenceEndpointSideColor, incidenceColorTripleData,
      incidenceSideColorAt, incidenceColors,
      firstTag, secondTag, thirdTag] using mapped
  have sidesNodup :
      (endpointTripleDataList actualData).map Prod.fst |>.Nodup := by
    rw [← compressedEq]
    dsimp [input, endpoints]
    simpa [endpointTripleDataList, endpointTripleData] using
      fan.sidesNodup
  have endpointTripleMember :
      endpoint ∈ problem.contractedTripleEndpoints :=
    endpoint.mem_contractedTripleEndpoints_of_vertex_triple
      endpointMember vertexEq
  have endpointDataEq :
      endpointSideColor (input, endpoint) =
        incidenceEndpointSideColor input endpoint := by
    exact presentation.toPlanarPresentation
      |>.compilerEndpointSideColor_eq_incidenceTag
        endpoint endpointTripleMember
  have headerDataEq :
      endpointHeaderData input endpoint =
        (⟨true, some actualData,
          incidenceEndpointSideColor input endpoint⟩ :
            EndpointHeaderData) := by
    unfold endpointHeaderData
    rw [vertexEq, dataAtEq, endpointDataEq]
    rfl
  rw [show inputOfPresentation presentation.toPlanarPresentation = input
    by rfl]
  rw [headerDataEq]
  exact EndpointHeaderData.choices_eq_of_perm
    true actualData canonicalData
    (incidenceEndpointSideColor input endpoint)
    dataPerm.symm sidesNodup

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
