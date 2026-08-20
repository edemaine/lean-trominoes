/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationContractedEndpointDirections
import LeanTrominoes.PeriodicThreeDMContractionGeometry
import LeanTrominoes.PeriodicThreeDMIncidenceVertexCoverage

/-! # Incidence directions at normalized contracted triple endpoints -/

namespace LeanTrominoes

open Gadget PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Every genuine incidence route in a compatible loopless presentation
contains at least its two distinct endpoint occurrences. -/
theorem PlanarPresentation.incidenceRoute_length_ge_two
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tag : IncidenceTag} (tagMember : tag ∈ problem.incidenceTags) :
    2 ≤ (presentation.incidenceRoute tag).length := by
  exact PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
    problem.incidenceGraph presentation.drawing presentation.compatible
    problem.incidenceGraph_edgesAreLoopless
    (presentation.incidenceRoute_mem tagMember)

/-- After translating and reversing a second incidence at a suppressed
element, its head is the first incidence's translated element endpoint. -/
theorem PlanarPresentation.reversedIncidenceRouteAt_head_of_incidence_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (secondMember : second ∈ problem.incidences color atom) :
    (presentation.reversedIncidenceRouteAt color first second).head? =
      some (Cell.add
        (presentation.drawing.vertexPosition problem.incidenceGraph
          (.element color atom))
        (presentation.drawing.periodTranslation first.offset)) := by
  have secondEndpoints :=
    presentation.incidenceRoute_endpoints_of_incidence
      color atom secondMember
  simp only [PlanarPresentation.reversedIncidenceRouteAt,
    List.head?_reverse, translatePolyline, List.getLast?_map,
    secondEndpoints.2, Option.map_some]
  simpa using
    periodTranslation_element_endpoint_sub
      presentation.drawing
      (presentation.drawing.vertexPosition problem.incidenceGraph
        (.element color atom))
      first.offset second.offset

/-- The compiler view of an emitted edge's source endpoint uses the first
direction of the incidence represented by its source tag. -/
theorem PlanarPresentation.compilerOutwardDirection_source_eq_incidence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat) (edge : ContractedEdge)
    (edgeMember :
      edge ∈ problem.contractedEdgesForElement color atom) :
    NormalizationCompiler.outwardDirection
        (NormalizationCompiler.inputOfPresentation presentation)
        (.source edge) =
      AxisDirection.polylineFirstDirection
        (NormalizationCompiler.incidenceRoute
          (NormalizationCompiler.inputOfPresentation presentation)
          edge.sourceTag) := by
  have metadata :=
    contractedEdgesForElement_metadata
      problem color atom edgeMember
  have incidenceMembers :=
    contractedEdgesForElement_incidence_members
      problem color atom edgeMember
  cases edge with
  | retained edgeColor edgeAtom incidence =>
      simp only [ContractedEdge.color, ContractedEdge.atom] at metadata
      rcases metadata with ⟨rfl, rfl⟩
      exact NormalizationCompiler.outwardDirection_source_retained
        _ edgeColor edgeAtom incidence
  | through edgeColor edgeAtom first second =>
      simp only [ContractedEdge.color, ContractedEdge.atom] at metadata
      rcases metadata with ⟨rfl, rfl⟩
      have firstMember :
          first ∈ problem.incidences edgeColor edgeAtom := by
        simpa [ContractedEdge.sourceIncidence] using incidenceMembers.1
      have tagMember :
          ⟨first.tripleIndex, edgeColor⟩ ∈ problem.incidenceTags :=
        incidenceTag_mem_of_incidence_mem
          problem edgeColor edgeAtom firstMember
      apply NormalizationCompiler.outwardDirection_source_through
      simpa [NormalizationCompiler.inputOfPresentation,
        NormalizationCompiler.incidenceRoute,
        PlanarPresentation.incidenceRoute] using
        presentation.incidenceRoute_length_ge_two tagMember

/-- The compiler view of an emitted suppressed edge's target triple endpoint
uses the first direction of its represented second incidence. -/
theorem PlanarPresentation.compilerOutwardDirection_target_through_eq_incidence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (edgeMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdgesForElement color atom) :
    NormalizationCompiler.outwardDirection
        (NormalizationCompiler.inputOfPresentation presentation)
        (.target (.through color atom first second)) =
      AxisDirection.polylineFirstDirection
        (NormalizationCompiler.incidenceRoute
          (NormalizationCompiler.inputOfPresentation presentation)
          ⟨second.tripleIndex, color⟩) := by
  have incidenceMembers :=
    contractedEdgesForElement_incidence_members
      problem color atom edgeMember
  have firstMember : first ∈ problem.incidences color atom := by
    simpa [ContractedEdge.sourceIncidence] using incidenceMembers.1
  have secondMember : second ∈ problem.incidences color atom := by
    simpa [ContractedEdge.targetIncidence] using incidenceMembers.2.1
  have firstEndpoints :=
    presentation.incidenceRoute_endpoints_of_incidence
      color atom firstMember
  have secondTagMember :
      ⟨second.tripleIndex, color⟩ ∈ problem.incidenceTags :=
    incidenceTag_mem_of_incidence_mem
      problem color atom secondMember
  let middle := Cell.add
    (presentation.drawing.vertexPosition problem.incidenceGraph
      (.element color atom))
    (presentation.drawing.periodTranslation first.offset)
  apply NormalizationCompiler.outwardDirection_target_through
    (middle := middle)
  · simpa [NormalizationCompiler.inputOfPresentation,
      NormalizationCompiler.incidenceRoute,
      PlanarPresentation.incidenceRoute, middle] using firstEndpoints.2
  · simpa [NormalizationCompiler.inputOfPresentation,
      NormalizationCompiler.reversedIncidenceRouteAt,
      NormalizationCompiler.incidenceRoute,
      PlanarPresentation.reversedIncidenceRouteAt,
      PlanarPresentation.incidenceRoute, middle] using
        presentation.reversedIncidenceRouteAt_head_of_incidence_mem
          color atom first second secondMember
  · simpa [NormalizationCompiler.inputOfPresentation,
      NormalizationCompiler.incidenceRoute,
      PlanarPresentation.incidenceRoute] using
        presentation.incidenceRoute_length_ge_two secondTagMember

end PeriodicThreeDM
end LeanTrominoes
