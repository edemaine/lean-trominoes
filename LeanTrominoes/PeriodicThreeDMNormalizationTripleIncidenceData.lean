/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationTripleEndpointDirections
import LeanTrominoes.PeriodicThreeDMNormalizationEndpointTripleDataAtComputability
import LeanTrominoes.PeriodicThreeDMContractedEndpointDegree

/-! # Triple normalization data from original incidence routes -/

noncomputable section

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM
namespace NormalizationCompiler

/-- Side/color data read directly from an original incidence tag, before
inspecting how its colored element was retained or suppressed. -/
def incidenceEndpointSideColor
    (input : Input) (endpoint : ContractedEndpoint) : EndpointSideColor :=
  (VertexSide.ofDirection
    (AxisDirection.polylineFirstDirection
      (incidenceRoute input endpoint.incidenceTag)),
    endpoint.incidenceTag.color)

/-- The three original-incidence records corresponding to one executable
endpoint triple, in that endpoint list's order. -/
def incidenceEndpointTripleData
    (input : Input) (endpoints : EndpointTriple) : EndpointTripleData :=
  (incidenceEndpointSideColor input endpoints.1,
    incidenceEndpointSideColor input endpoints.2.1,
    incidenceEndpointSideColor input endpoints.2.2)

/-- At a triple vertex, all three compressed compiler endpoint records can
be read directly from their original incidence routes. -/
theorem compilerEndpointTripleData_eq_incidenceTags
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (tripleIndex : Nat) (first second third : ContractedEndpoint)
    (endpointsEq :
      problem.contractedEndpointsAt (.triple tripleIndex) =
        [first, second, third]) :
    endpointTripleData
        (inputOfPresentation presentation, (first, second, third)) =
      incidenceEndpointTripleData
        (inputOfPresentation presentation) (first, second, third) := by
  have firstAt :
      first ∈ problem.contractedEndpointsAt (.triple tripleIndex) := by
    rw [endpointsEq]
    simp
  have secondAt :
      second ∈ problem.contractedEndpointsAt (.triple tripleIndex) := by
    rw [endpointsEq]
    simp
  have thirdAt :
      third ∈ problem.contractedEndpointsAt (.triple tripleIndex) := by
    rw [endpointsEq]
    simp
  have firstData :=
    (contractedEndpointsAt_mem_iff problem _ first).mp firstAt
  have secondData :=
    (contractedEndpointsAt_mem_iff problem _ second).mp secondAt
  have thirdData :=
    (contractedEndpointsAt_mem_iff problem _ third).mp thirdAt
  have firstTriple :=
    first.mem_contractedTripleEndpoints_of_vertex_triple
      firstData.1 firstData.2
  have secondTriple :=
    second.mem_contractedTripleEndpoints_of_vertex_triple
      secondData.1 secondData.2
  have thirdTriple :=
    third.mem_contractedTripleEndpoints_of_vertex_triple
      thirdData.1 thirdData.2
  unfold endpointTripleData incidenceEndpointTripleData
    incidenceEndpointSideColor
  rw [presentation.compilerEndpointSideColor_eq_incidenceTag
      first firstTriple,
    presentation.compilerEndpointSideColor_eq_incidenceTag
      second secondTriple,
    presentation.compilerEndpointSideColor_eq_incidenceTag
      third thirdTriple]

/-- Thus the optional finite datum used by `finalVertexCellType` is some
triple of original-incidence directions at every genuine triple index. -/
theorem exists_endpointTripleDataAt_eq_incidenceTags
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length) :
    ∃ endpoints : EndpointTriple,
      endpointTripleDataAt
          (inputOfPresentation presentation, .triple tripleIndex) =
        some (incidenceEndpointTripleData
          (inputOfPresentation presentation) endpoints) := by
  rcases exists_contractedEndpointsAt_triple_eq
      problem wellFormed degree tripleIndex indexLt with
    ⟨first, second, third, endpointsEq⟩
  refine ⟨(first, second, third), ?_⟩
  unfold endpointTripleDataAt endpointTripleAt
  simp only [inputOfPresentation]
  rw [endpointsEq]
  simp only
  exact congrArg some
    (compilerEndpointTripleData_eq_incidenceTags presentation
      tripleIndex first second third endpointsEq)

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
