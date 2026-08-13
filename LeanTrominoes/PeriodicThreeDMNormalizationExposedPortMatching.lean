/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRoutePortMatching

/-!
# Matching every exposed port in the compiled final lookup

The assignment lookup can return either a normalized vertex or a route
interior.  Vertex-port completeness recovers the owning endpoint in the first
case, while route-port completeness recovers the owning route triple in the
second.  The local matching theorems then show that the finite torus neighbor
has the same color on its opposite side.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- A finite position is determined by its stored integer representatives. -/
theorem PlanarPresentation.position_eq_normalizedPositionAt_of_values_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (position : presentation.normalizedOrthogonalDrawing.Position)
    (point : Cell)
    (valuesEqual :
      (((position.1.val : Int), (position.2.val : Int))) =
        rasterLocation presentation.finalNormalizationPeriod point) :
    position = presentation.normalizedPositionAt point := by
  have normalizedValues := presentation.normalizedPositionAt_values point
  have representativesEqual := valuesEqual.trans normalizedValues.symm
  apply Prod.ext
  · apply Fin.ext
    have horizontalEqual :
        (position.1.val : Int) =
          ((presentation.normalizedPositionAt point).1.val : Int) := by
      simpa using congrArg Prod.fst representativesEqual
    exact_mod_cast horizontalEqual
  · apply Fin.ext
    have verticalEqual :
        (position.2.val : Int) =
          ((presentation.normalizedPositionAt point).2.val : Int) := by
      simpa using congrArg Prod.snd representativesEqual
    exact_mod_cast verticalEqual

/-- Once a finite position represents a geometric point, its finite neighbor
represents the corresponding geometric unit step. -/
theorem PlanarPresentation.neighbor_values_eq_raster_add_side_step
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (position : presentation.normalizedOrthogonalDrawing.Position)
    (point : Cell) (side : Side)
    (valuesEqual :
      (((position.1.val : Int), (position.2.val : Int))) =
        rasterLocation presentation.finalNormalizationPeriod point) :
    ((((presentation.normalizedOrthogonalDrawing.neighbor position side).1.val :
          Int),
        ((presentation.normalizedOrthogonalDrawing.neighbor position side).2.val :
          Int))) =
      rasterLocation presentation.finalNormalizationPeriod
        (Cell.add point (axisDirectionOfSide side).step) := by
  have positionEqual :=
    presentation.position_eq_normalizedPositionAt_of_values_eq
      position point valuesEqual
  have neighborEqual :
      presentation.normalizedOrthogonalDrawing.neighbor position side =
        presentation.normalizedPositionAt
          (Cell.add point (axisDirectionOfSide side).step) := by
    rw [positionEqual]
    symm
    simpa using presentation.normalizedPositionAt_add_step point
      (axisDirectionOfSide_isGenuine side)
  have representativesEqual := congrArg
    (fun finitePosition : presentation.normalizedOrthogonalDrawing.Position =>
      (((finitePosition.1.val : Int), (finitePosition.2.val : Int))))
    neighborEqual
  exact representativesEqual.trans
    (presentation.normalizedPositionAt_values
      (Cell.add point (axisDirectionOfSide side).step))

/-- Equal raster locations remain equal after adding the same geometric
offset. -/
theorem rasterLocation_add_eq_of_eq
    (period : Nat) {first second : Cell}
    (equal : rasterLocation period first = rasterLocation period second)
    (offset : Cell) :
    rasterLocation period (Cell.add first offset) =
      rasterLocation period (Cell.add second offset) := by
  rcases (rasterLocation_eq_iff_exists_periodTranslation
      period first second).mp equal with ⟨translation, geometricEqual⟩
  apply (rasterLocation_eq_iff_exists_periodTranslation period _ _).mpr
  refine ⟨translation, ?_⟩
  rw [geometricEqual]
  rcases second with ⟨secondX, secondY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  rcases translation with ⟨translationX, translationY⟩
  simp only [Cell.add, Cell.scale, Prod.mk.injEq]
  constructor <;> ring

/-- A canonical port's stored direction is exactly the geometric direction
corresponding to its drawing-cell side. -/
@[simp]
theorem axisDirectionOfSide_canonicalPort_side
    (port : CanonicalVertexPort) :
    axisDirectionOfSide port.side = port.direction := by
  cases port <;>
    rfl

/-- Every exposed port returned by the compiled lookup has a matching colored
port at the finite torus neighbor. -/
theorem ContinuousPlanarPresentation.finalCellTypeAt_neighbor_portColor
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (position :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.Position)
    (side : Side) (color : WireColor)
    (exposed :
      (presentation.toPlanarPresentation.finalCellTypeAt
        (((position.1.val : Int), (position.2.val : Int)))).portColor side =
          some color) :
    (presentation.toPlanarPresentation.finalCellTypeAt
      ((((presentation.toPlanarPresentation.normalizedOrthogonalDrawing.neighbor
          position side).1.val : Int),
        ((presentation.toPlanarPresentation.normalizedOrthogonalDrawing.neighbor
          position side).2.val : Int)))).portColor side.opposite =
            some color := by
  let planar := presentation.toPlanarPresentation
  let location : Cell :=
    (((position.1.val : Int), (position.2.val : Int)))
  unfold PlanarPresentation.finalCellTypeAt at exposed
  generalize lookupEqual : planar.finalCellAssignments.lookup location = result
    at exposed
  cases result with
  | none => simp [OrthogonalCellType.portColor] at exposed
  | some cellType =>
      simp only [Option.getD_some] at exposed
      have assignmentMember : (location, cellType) ∈
          planar.finalCellAssignments :=
        List.mem_of_lookup_eq_some lookupEqual
      simp only [PlanarPresentation.finalCellAssignments,
        List.mem_append] at assignmentMember
      rcases assignmentMember with vertexMember | routeMember
      · simp only [PlanarPresentation.finalVertexAssignments,
          List.mem_map] at vertexMember
        rcases vertexMember with
          ⟨vertex, vertexListed, assignmentEqual⟩
        have locationEqual : location =
            rasterLocation planar.finalNormalizationPeriod
              (planar.finalNormalizationPosition vertex) :=
          (congrArg Prod.fst assignmentEqual).symm
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
          planar.neighbor_values_eq_raster_add_side_step position
            (planar.finalNormalizationPosition vertex) side locationEqual
        change
          (planar.finalCellTypeAt
            ((((planar.normalizedOrthogonalDrawing.neighbor position side).1.val :
                Int),
              ((planar.normalizedOrthogonalDrawing.neighbor position side).2.val :
                Int)))).portColor side.opposite = some color
        rw [neighborValues]
        have currentColor :
            (planar.finalCellTypeAt
              (rasterLocation planar.finalNormalizationPeriod
                (planar.finalNormalizationPosition vertex))).portColor side =
              some color := by
          rw [planar.finalCellTypeAt_vertex collisionFree vertexListed]
          exact exposedVertex
        have edgeMember := endpoint.edge_mem_of_mem endpointMember
        cases endpoint with
        | source edge =>
            simp only [ContractedEndpoint.vertex] at endpointVertex
            have portsMatch :=
              PlanarPresentation.finalCellTypeAt_source_port_matches
                (presentation := presentation) wellFormed degree collisionFree
                edgeMember
            have specialized :
                (planar.finalCellTypeAt
                  (rasterLocation planar.finalNormalizationPeriod
                    (planar.finalNormalizationPosition vertex))).portColor side =
                (planar.finalCellTypeAt
                  (rasterLocation planar.finalNormalizationPeriod
                    (Cell.add (planar.finalNormalizationPosition vertex)
                      (axisDirectionOfSide side).step))).portColor
                    side.opposite := by
              rw [← endpointVertex, ← endpointSide]
              rw [axisDirectionOfSide_canonicalPort_side]
              exact portsMatch
            rw [← specialized]
            exact currentColor
        | target edge =>
            simp only [ContractedEndpoint.vertex] at endpointVertex
            have portsMatch :=
              PlanarPresentation.finalCellTypeAt_target_port_matches
                (presentation := presentation) wellFormed degree collisionFree
                edgeMember
            have occurrenceEqual := planar.rasterLocation_finalTargetOccurrence edge
            have adjacentEqual := rasterLocation_add_eq_of_eq
              planar.finalNormalizationPeriod occurrenceEqual
              ((ContractedEndpoint.target edge).finalNormalizedPort planar).direction.step
            have specialized :
                (planar.finalCellTypeAt
                  (rasterLocation planar.finalNormalizationPeriod
                    (planar.finalNormalizationPosition vertex))).portColor side =
                (planar.finalCellTypeAt
                  (rasterLocation planar.finalNormalizationPeriod
                    (Cell.add (planar.finalNormalizationPosition vertex)
                      (axisDirectionOfSide side).step))).portColor
                    side.opposite := by
              rw [← endpointVertex, ← endpointSide]
              rw [axisDirectionOfSide_canonicalPort_side]
              rw [← adjacentEqual]
              exact portsMatch
            rw [← specialized]
            exact currentColor
      · rcases planar.exists_final_route_triple_of_assignment_mem routeMember with
          ⟨edge, edgeMember, leading, before, current, after, rest,
            routeEquation, assignmentEqual⟩
        have locationEqual : location =
            rasterLocation planar.finalNormalizationPeriod current :=
          congrArg Prod.fst assignmentEqual
        have cellTypeEqual : cellType =
            routingCellTypeAt before current after edge.color :=
          congrArg Prod.snd assignmentEqual
        have exposedRoute :
            (routingCellTypeAt before current after edge.color).portColor side =
              some color := by
          rw [← cellTypeEqual]
          exact exposed
        have portsMatch :=
          presentation.finalCellTypeAt_routeTriple_port_matches
            wellFormed degree collisionFree edgeMember leading before current
              after rest routeEquation side color exposedRoute
        have currentColor :
            (planar.finalCellTypeAt
              (rasterLocation planar.finalNormalizationPeriod current)).portColor
                side = some color := by
          rw [planar.finalCellTypeAt_routeTriple collisionFree edgeMember
            leading before current after rest routeEquation]
          exact exposedRoute
        have neighborValues :=
          planar.neighbor_values_eq_raster_add_side_step position current side
            locationEqual
        change
          (planar.finalCellTypeAt
            ((((planar.normalizedOrthogonalDrawing.neighbor position side).1.val :
                Int),
              ((planar.normalizedOrthogonalDrawing.neighbor position side).2.val :
                Int)))).portColor side.opposite = some color
        rw [neighborValues]
        rw [← portsMatch]
        exact currentColor

end PeriodicThreeDM
end LeanTrominoes
