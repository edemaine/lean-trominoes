/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripCellAssignmentBounds
import LeanTrominoes.PeriodicThreeDMNormalizationStripPositionGeometry
import LeanTrominoes.PeriodicThreeDMNormalizationStripRoutePortMatching

/-!
# Matching every exposed port in the normalized 3DM strip
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Equal strip locations remain equal after adding the same geometric
offset. -/
theorem stripRasterLocation_add_eq_of_eq
    (period : Nat) {first second : Cell}
    (equal : stripRasterLocation period first =
      stripRasterLocation period second)
    (offset : Cell) :
    stripRasterLocation period (Cell.add first offset) =
      stripRasterLocation period (Cell.add second offset) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp only [stripRasterLocation, Prod.mk.injEq] at equal
  simp only [stripRasterLocation, Cell.add, Prod.mk.injEq]
  constructor
  · have horizontalMod :
        firstX ≡ secondX [ZMOD (period : Int)] := equal.1
    exact horizontalMod.add_right offsetX
  · have verticalEqual : firstY = secondY := by omega
    rw [verticalEqual]

/-- A canonical port's stored direction is the geometric direction
corresponding to its drawing-cell side. -/
@[simp]
theorem axisDirectionOfSide_stripCanonicalPort_side
    (port : CanonicalVertexPort) :
    axisDirectionOfSide port.side = port.direction := by
  cases port <;> rfl

/-- Every exposed colored port returned by the strip lookup has the same
color on the opposite port of its finite neighbor. -/
theorem ContinuousPlanarPresentation.finalStripCellTypeAt_neighbor_portColor
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
    (position :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing.Position)
    (side : Side) (color : WireColor)
    (exposed :
      (presentation.toPlanarPresentation.finalStripCellTypeAt
        (((position.1.val : Int), (position.2.val : Int)))).portColor side =
          some color) :
    (presentation.toPlanarPresentation.finalStripCellTypeAt
      ((((presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing.neighbor
          position side).1.val : Int),
        ((presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing.neighbor
          position side).2.val : Int)))).portColor side.opposite =
            some color := by
  let planar := presentation.toPlanarPresentation
  let location : Cell :=
    (((position.1.val : Int), (position.2.val : Int)))
  unfold PlanarPresentation.finalStripCellTypeAt at exposed
  generalize lookupEqual :
      planar.finalStripCellAssignments.lookup location = result at exposed
  cases result with
  | none => simp [OrthogonalCellType.portColor] at exposed
  | some cellType =>
      simp only [Option.getD_some] at exposed
      have wholeAssignmentMember : (location, cellType) ∈
          planar.finalStripCellAssignments :=
        List.mem_of_lookup_eq_some lookupEqual
      have locationInterior :
          0 < location.2 ∧
            location.2 < 3 * planar.finalNormalizationPeriod :=
        presentation.finalStripCellAssignment_vertical_interior
          wellFormed degree horizontal sourceInside wholeAssignmentMember
      have assignmentMember := wholeAssignmentMember
      simp only [PlanarPresentation.finalStripCellAssignments,
        List.mem_append] at assignmentMember
      rcases assignmentMember with vertexMember | routeMember
      · simp only [PlanarPresentation.finalStripVertexAssignments,
          List.mem_map] at vertexMember
        rcases vertexMember with
          ⟨vertex, vertexListed, assignmentEqual⟩
        have locationEqual : location =
            stripRasterLocation planar.finalNormalizationPeriod
              (planar.finalNormalizationPosition vertex) :=
          (congrArg Prod.fst assignmentEqual).symm
        have pointInterior :
            0 < (stripRasterLocation planar.finalNormalizationPeriod
                (planar.finalNormalizationPosition vertex)).2 ∧
              (stripRasterLocation planar.finalNormalizationPeriod
                (planar.finalNormalizationPosition vertex)).2 <
                3 * planar.finalNormalizationPeriod := by
          rw [← locationEqual]
          exact locationInterior
        have cellTypeEqual : planar.finalVertexCellType vertex = cellType :=
          congrArg Prod.snd assignmentEqual
        have exposedVertex :
            (planar.finalVertexCellType vertex).portColor side =
              some color := by
          rw [cellTypeEqual]
          exact exposed
        rcases
            PlanarPresentation.exists_endpoint_of_finalVertexCellType_portColor_eq_some
              (presentation := presentation) wellFormed degree vertexListed
              exposedVertex with
          ⟨endpoint, endpointMember, endpointVertex, endpointSide,
            endpointColor⟩
        have neighborValues :=
          planar.stripNeighbor_values_eq_raster_add_side_step position
            (planar.finalNormalizationPosition vertex) side pointInterior
            locationEqual
        change
          (planar.finalStripCellTypeAt
            ((((planar.stripNormalizedOrthogonalDrawing.neighbor
                position side).1.val : Int),
              ((planar.stripNormalizedOrthogonalDrawing.neighbor
                position side).2.val : Int)))).portColor side.opposite = some color
        rw [neighborValues]
        have currentColor :
            (planar.finalStripCellTypeAt
              (stripRasterLocation planar.finalNormalizationPeriod
                (planar.finalNormalizationPosition vertex))).portColor side =
              some color := by
          rw [planar.finalStripCellTypeAt_vertex collisionFree vertexListed]
          exact exposedVertex
        have edgeMember := endpoint.edge_mem_of_mem endpointMember
        cases endpoint with
        | source edge =>
            simp only [ContractedEndpoint.vertex] at endpointVertex
            have portsMatch :=
              PlanarPresentation.finalStripCellTypeAt_source_port_matches
                (presentation := presentation) wellFormed degree collisionFree
                edgeMember
            have specialized :
                (planar.finalStripCellTypeAt
                  (stripRasterLocation planar.finalNormalizationPeriod
                    (planar.finalNormalizationPosition vertex))).portColor side =
                (planar.finalStripCellTypeAt
                  (stripRasterLocation planar.finalNormalizationPeriod
                    (Cell.add (planar.finalNormalizationPosition vertex)
                      (axisDirectionOfSide side).step))).portColor
                    side.opposite := by
              rw [← endpointVertex, ← endpointSide]
              rw [axisDirectionOfSide_stripCanonicalPort_side]
              exact portsMatch
            rw [← specialized]
            exact currentColor
        | target edge =>
            simp only [ContractedEndpoint.vertex] at endpointVertex
            have edgeMember' : edge ∈ problem.contractedEdges := by
              simpa using edgeMember
            have portsMatch :=
              PlanarPresentation.finalStripCellTypeAt_target_port_matches
                (presentation := presentation) (edge := edge)
                wellFormed degree collisionFree edgeMember'
            have occurrenceEqual :=
              planar.stripRasterLocation_finalTargetOccurrence
                horizontal (edge := edge) edgeMember'
            have adjacentEqual := stripRasterLocation_add_eq_of_eq
              planar.finalNormalizationPeriod occurrenceEqual
              ((ContractedEndpoint.target edge).finalNormalizedPort
                planar).direction.step
            have specialized :
                (planar.finalStripCellTypeAt
                  (stripRasterLocation planar.finalNormalizationPeriod
                    (planar.finalNormalizationPosition vertex))).portColor side =
                (planar.finalStripCellTypeAt
                  (stripRasterLocation planar.finalNormalizationPeriod
                    (Cell.add (planar.finalNormalizationPosition vertex)
                      (axisDirectionOfSide side).step))).portColor
                    side.opposite := by
              rw [← endpointVertex, ← endpointSide]
              rw [axisDirectionOfSide_stripCanonicalPort_side]
              rw [← adjacentEqual]
              exact portsMatch
            rw [← specialized]
            exact currentColor
      · rcases planar.exists_final_strip_route_triple_of_assignment_mem
          routeMember with
          ⟨edge, edgeMember, leading, before, current, after, rest,
            routeEquation, assignmentEqual⟩
        have locationEqual : location =
            stripRasterLocation planar.finalNormalizationPeriod current :=
          congrArg Prod.fst assignmentEqual
        have pointInterior :
            0 < (stripRasterLocation planar.finalNormalizationPeriod current).2 ∧
              (stripRasterLocation planar.finalNormalizationPeriod current).2 <
                3 * planar.finalNormalizationPeriod := by
          rw [← locationEqual]
          exact locationInterior
        have cellTypeEqual : cellType =
            routingCellTypeAt before current after edge.color :=
          congrArg Prod.snd assignmentEqual
        have exposedRoute :
            (routingCellTypeAt before current after edge.color).portColor side =
              some color := by
          rw [← cellTypeEqual]
          exact exposed
        have portsMatch :=
          presentation.finalStripCellTypeAt_routeTriple_port_matches
            wellFormed degree horizontal collisionFree edgeMember leading before
              current after rest routeEquation side color exposedRoute
        have currentColor :
            (planar.finalStripCellTypeAt
              (stripRasterLocation planar.finalNormalizationPeriod current)).portColor
                side = some color := by
          rw [planar.finalStripCellTypeAt_routeTriple collisionFree edgeMember
            leading before current after rest routeEquation]
          exact exposedRoute
        have neighborValues :=
          planar.stripNeighbor_values_eq_raster_add_side_step position current side
            pointInterior locationEqual
        change
          (planar.finalStripCellTypeAt
            ((((planar.stripNormalizedOrthogonalDrawing.neighbor
                position side).1.val : Int),
              ((planar.stripNormalizedOrthogonalDrawing.neighbor
                position side).2.val : Int)))).portColor side.opposite = some color
        rw [neighborValues]
        rw [← portsMatch]
        exact currentColor

end PeriodicThreeDM
end LeanTrominoes
