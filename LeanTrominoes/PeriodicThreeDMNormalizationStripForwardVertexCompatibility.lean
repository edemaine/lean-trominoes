/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationForwardVertexCompatibility
import LeanTrominoes.PeriodicThreeDMNormalizationStripForwardRouteCompatibility

/-!
# Forward-orientation compatibility at normalized strip vertices

Every exposed strip vertex port selects a unique contracted endpoint.  Source
ports use the same block translate; target ports use the source block obtained
by subtracting the edge offset.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Every exposed port of every explicit normalized strip vertex occurrence is
compatible with its drawing-lattice neighbor. -/
theorem ContinuousPlanarPresentation.forwardStripDrawingOrientation_vertex_neighbor
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices)
    (translate : Cell) (side : Side) (color : WireColor)
    (exposed :
      (presentation.toPlanarPresentation.finalVertexCellType vertex).portColor
        side = some color) :
    let planar := presentation.toPlanarPresentation
    let location := Cell.add
      (stripReflectedLocation planar.finalNormalizationPeriod
        (planar.finalNormalizationPosition vertex))
      (planar.stripPeriodTranslation translate)
    presentation.forwardStripDrawingOrientation values location side =
      !(presentation.forwardStripDrawingOrientation values
        (PeriodicOrthogonalDrawing.latticeNeighbor location side)
        side.opposite) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  have endpointData :=
    PlanarPresentation.endpointAtVertexPort_data_of_exposed
      presentation wellFormed degree vertexMember exposed
  generalize endpointEq : planar.endpointAtVertexPort vertex side = selected
    at endpointData
  change selected ∈ problem.contractedEndpoints ∧
      selected.vertex = vertex ∧
      (selected.finalNormalizedPort planar).side = side ∧
      selected.color = color at endpointData
  rcases endpointData with
    ⟨endpointMember, endpointVertex, endpointSide, endpointColor⟩
  cases selected with
  | source edge =>
      simp only [ContractedEndpoint.vertex] at endpointVertex
      subst vertex
      subst side
      have edgeMember :=
        (ContractedEndpoint.source edge).edge_mem_of_mem endpointMember
      exact presentation.forwardStripDrawingOrientation_source_neighbor
        wellFormed degree horizontal sourceInside collisionFree values
          edgeMember translate
  | target edge =>
      simp only [ContractedEndpoint.vertex] at endpointVertex
      subst vertex
      subst side
      have edgeMember :=
        (ContractedEndpoint.target edge).edge_mem_of_mem endpointMember
      let sourceTranslate := Cell.sub translate edge.toPeriodicEdge.offset
      have compatibility :=
        presentation.forwardStripDrawingOrientation_target_neighbor
          wellFormed degree horizontal sourceInside collisionFree values valid
            (edge := edge) edgeMember sourceTranslate
      have occurrenceEq :
          Cell.add
              (stripReflectedLocation planar.finalNormalizationPeriod
                (normalizeVertexPosition (planar.normalizationTarget2 edge)))
              (planar.stripPeriodTranslation sourceTranslate) =
            Cell.add
              (stripReflectedLocation planar.finalNormalizationPeriod
                (planar.finalNormalizationPosition edge.toPeriodicEdge.target))
              (planar.stripPeriodTranslation translate) := by
        rw [planar.finalTargetOccurrence_add_stripPeriodTranslation
          horizontal (edge := edge) edgeMember sourceTranslate]
        simp [sourceTranslate, Cell.add_sub_right_cancel]
      dsimp only at compatibility
      rw [occurrenceEq] at compatibility
      exact compatibility

end PeriodicThreeDM

end LeanTrominoes
