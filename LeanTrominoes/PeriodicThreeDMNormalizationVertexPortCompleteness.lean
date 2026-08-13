/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationFinalAssignmentCollisionFreedom
import LeanTrominoes.PeriodicThreeDMVertexNormalizationEndpointColors

/-!
# Completeness of final normalized vertex ports

Endpoint color correctness gives the forward direction: every endpoint finds
its edge color at its final port.  This module proves the converse needed by
raster matching: every exposed port of a retained final vertex belongs to one
of its three contracted endpoints.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Distinct endpoints at one vertex still occupy distinct ports after both
cyclic permutations. -/
theorem ContractedEndpoint.finalNormalizedPort_ne
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (secondMember : second ∈ problem.contractedEndpoints)
    (different : first ≠ second)
    (sameVertex : first.vertex = second.vertex) :
    first.finalNormalizedPort presentation.toPlanarPresentation ≠
      second.finalNormalizedPort presentation.toPlanarPresentation := by
  let planar := presentation.toPlanarPresentation
  have portsDifferent := first.secondNormalizedPort_ne
    presentation wellFormed degree firstMember secondMember
      different sameVertex
  unfold ContractedEndpoint.finalNormalizedPort
  rw [sameVertex]
  intro equal
  exact portsDifferent
    (rotationRoundPort_injective
      (secondRotationActive planar second.vertex) equal)

/-- Three pairwise distinct canonical ports exhaust the three-element port
type. -/
theorem CanonicalVertexPort.eq_first_or_eq_second_or_eq_third
    (first second third port : CanonicalVertexPort)
    (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third)
    (secondNeThird : second ≠ third) :
    port = first ∨ port = second ∨ port = third := by
  cases first <;> cases second <;> cases third <;> cases port <;>
    simp_all

/-- The three endpoints of a contracted fan occupy all three final
canonical ports. -/
theorem ContractedVertexFan.exists_endpoint_finalNormalizedPort_eq
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (fan : ContractedVertexFan presentation vertex)
    (port : CanonicalVertexPort) :
    ∃ endpoint ∈ [fan.first, fan.second, fan.third],
      endpoint.finalNormalizedPort presentation.toPlanarPresentation = port := by
  have firstSecond := fan.first.finalNormalizedPort_ne
    presentation wellFormed degree fan.first_data.1 fan.second_data.1
      (fan.first_ne_second degree)
      (fan.first_data.2.trans fan.second_data.2.symm)
  have firstThird := fan.first.finalNormalizedPort_ne
    presentation wellFormed degree fan.first_data.1 fan.third_data.1
      (fan.first_ne_third degree)
      (fan.first_data.2.trans fan.third_data.2.symm)
  have secondThird := fan.second.finalNormalizedPort_ne
    presentation wellFormed degree fan.second_data.1 fan.third_data.1
      (fan.second_ne_third degree)
      (fan.second_data.2.trans fan.third_data.2.symm)
  rcases CanonicalVertexPort.eq_first_or_eq_second_or_eq_third
      (fan.first.finalNormalizedPort presentation.toPlanarPresentation)
      (fan.second.finalNormalizedPort presentation.toPlanarPresentation)
      (fan.third.finalNormalizedPort presentation.toPlanarPresentation)
      port firstSecond firstThird secondThird with
    equal | equal | equal
  · exact ⟨fan.first, by simp, equal.symm⟩
  · exact ⟨fan.second, by simp, equal.symm⟩
  · exact ⟨fan.third, by simp, equal.symm⟩

/-- A fan endpoint selected by a canonical port supplies the corresponding
exposed vertex-cell color. -/
theorem ContractedVertexFan.exists_endpoint_of_portColor_eq_some
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (fan : ContractedVertexFan presentation vertex)
    (southNone :
      (presentation.toPlanarPresentation.finalVertexCellType vertex).portColor
        .south = none)
    {side : Side} {color : WireColor}
    (exposed :
      (presentation.toPlanarPresentation.finalVertexCellType vertex).portColor
        side = some color) :
    ∃ endpoint ∈ problem.contractedEndpoints,
      endpoint.vertex = vertex ∧
        (endpoint.finalNormalizedPort
          presentation.toPlanarPresentation).side = side ∧
        endpoint.color = color := by
  have select (port : CanonicalVertexPort)
      (portSide : port.side = side) :
      ∃ endpoint ∈ problem.contractedEndpoints,
        endpoint.vertex = vertex ∧
          (endpoint.finalNormalizedPort
            presentation.toPlanarPresentation).side = side ∧
          endpoint.color = color := by
    rcases fan.exists_endpoint_finalNormalizedPort_eq
        wellFormed degree port with ⟨endpoint, endpointFanMember, portEq⟩
    have endpointAt : endpoint ∈ problem.contractedEndpointsAt vertex := by
      rw [fan.endpoints_eq]
      exact endpointFanMember
    have endpointData :=
      (contractedEndpointsAt_mem_iff problem vertex endpoint).mp endpointAt
    have endpointColor :=
      PlanarPresentation.finalVertexCellType_portColor_endpoint
        (presentation := presentation) wellFormed degree endpointData.1
    rw [endpointData.2, portEq, portSide] at endpointColor
    exact ⟨endpoint, endpointData.1, endpointData.2,
      portEq ▸ portSide, Option.some.inj (endpointColor.symm.trans exposed)⟩
  cases side with
  | north => exact select .north rfl
  | east => exact select .east rfl
  | south => rw [southNone] at exposed; contradiction
  | west => exact select .west rfl

/-- Every nonempty port of a retained final normalized vertex is owned by a
contracted endpoint with the same vertex, side, and color. -/
theorem PlanarPresentation.exists_endpoint_of_finalVertexCellType_portColor_eq_some
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices)
    {side : Side} {color : WireColor}
    (exposed :
      (presentation.toPlanarPresentation.finalVertexCellType vertex).portColor
        side = some color) :
    ∃ endpoint ∈ problem.contractedEndpoints,
      endpoint.vertex = vertex ∧
        (endpoint.finalNormalizedPort
          presentation.toPlanarPresentation).side = side ∧
        endpoint.color = color := by
  cases vertexEquation : vertex with
  | triple tripleIndex =>
      have indexLt : tripleIndex < problem.triples.length := by
        rw [vertexEquation] at vertexMember
        simpa [contractedGraph, tripleVertices,
          contractedElementVertices,
          contractedElementVerticesForColor] using vertexMember
      obtain ⟨fan⟩ := exists_contractVertexFan_at_triple
        presentation wellFormed degree tripleIndex indexLt
      have ports :=
        PlanarPresentation.finalVertexCellType_portColors_triple
          presentation wellFormed degree tripleIndex indexLt
      exact fan.exists_endpoint_of_portColor_eq_some
        wellFormed degree (by simpa [vertexEquation] using ports.2.2.2)
        (by simpa [vertexEquation] using exposed)
  | element elementColor atom =>
      have atomData : atom < problem.elementCount elementColor ∧
          problem.degree elementColor atom = 3 := by
        rw [vertexEquation] at vertexMember
        simp [contractedGraph, tripleVertices,
          contractedElementVertices,
          contractedElementVerticesForColor,
          incidenceColors] at vertexMember
        cases elementColor <;> simp_all
      obtain ⟨fan⟩ := exists_contractVertexFan_at_element
        presentation degree elementColor atom atomData.1 atomData.2
      have ports :=
        presentation.toPlanarPresentation
          |>.finalVertexCellType_portColors_element elementColor atom
      exact fan.exists_endpoint_of_portColor_eq_some
        wellFormed degree (by simpa [vertexEquation] using ports.2.2.2)
        (by simpa [vertexEquation] using exposed)

end PeriodicThreeDM
end LeanTrominoes
