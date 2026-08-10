import LeanTrominoes.PeriodicThreeDMNormalizationForwardRouteCompatibility

/-!
# Forward-orientation compatibility at normalized vertices

Every exposed normalized vertex port selects a unique contracted endpoint.
This module dispatches that endpoint to the source or translated-target
compatibility theorem, giving one statement for arbitrary vertex sites.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Adding back a componentwise-subtracted cell cancels the subtraction. -/
@[simp]
theorem Cell.add_sub_right_cancel (first second : Cell) :
    Cell.add (Cell.sub first second) second = first := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [Cell.add, Cell.sub]

/-- Every exposed port of every explicit normalized vertex occurrence is
compatible with its drawing-lattice neighbor. -/
theorem ContinuousPlanarPresentation.forwardDrawingOrientation_vertex_neighbor
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices)
    (translate : Cell) (side : Side) (color : WireColor)
    (exposed :
      (presentation.toPlanarPresentation.finalVertexCellType vertex).portColor
        side = some color) :
    let planar := presentation.toPlanarPresentation
    let location := reflectedLocation
      (Cell.add (planar.finalNormalizationPosition vertex)
        (Cell.scale (planar.finalNormalizationPeriod : Int) translate))
    presentation.forwardDrawingOrientation values location side =
      !(presentation.forwardDrawingOrientation values
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
      exact presentation.forwardDrawingOrientation_source_neighbor
        wellFormed degree collisionFree values edgeMember translate
  | target edge =>
      simp only [ContractedEndpoint.vertex] at endpointVertex
      subst vertex
      subst side
      have edgeMember :=
        (ContractedEndpoint.target edge).edge_mem_of_mem endpointMember
      have compatibility :=
        presentation.forwardDrawingOrientation_target_neighbor
          wellFormed degree collisionFree values valid (edge := edge) edgeMember
            (Cell.sub translate edge.toPeriodicEdge.offset)
      have occurrenceEq :
          Cell.add
              (normalizeVertexPosition (planar.normalizationTarget2 edge))
              (Cell.scale (planar.finalNormalizationPeriod : Int)
                (Cell.sub translate edge.toPeriodicEdge.offset)) =
            Cell.add
              (planar.finalNormalizationPosition edge.toPeriodicEdge.target)
              (Cell.scale (planar.finalNormalizationPeriod : Int)
                translate) := by
        simpa using
          planar.finalTargetOccurrence_add_periodTranslation edge
            (Cell.sub translate edge.toPeriodicEdge.offset)
      dsimp only at compatibility
      rw [occurrenceEq] at compatibility
      exact compatibility

end PeriodicThreeDM

end LeanTrominoes
