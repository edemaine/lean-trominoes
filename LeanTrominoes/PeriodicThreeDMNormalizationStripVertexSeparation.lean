/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentGeometry
import LeanTrominoes.PeriodicThreeDMNormalizationStripPositionGeometry
import LeanTrominoes.PeriodicThreeDMNormalizationStripRasterizationCorrectness
import LeanTrominoes.PeriodicThreeDMNormalizationStripVertexBounds

/-!
# Separation of normalized 3DM strip vertex cells
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Every assignment emitted from a strip route has a nonvertex cell type. -/
theorem stripRouteInteriorAssignments_isVertex_false
    (period : Nat) (color : WireColor) :
    ∀ {route : List Cell} {assignment : NormalizedCellAssignment},
      assignment ∈ stripRouteInteriorAssignments period color route →
        assignment.2.isVertex = false
  | [], _, member => by simp [stripRouteInteriorAssignments] at member
  | [_], _, member => by simp [stripRouteInteriorAssignments] at member
  | [_, _], _, member => by simp [stripRouteInteriorAssignments] at member
  | before :: current :: after :: rest, assignment, member => by
      simp only [stripRouteInteriorAssignments, List.mem_cons] at member
      rcases member with equal | tailMember
      · subst assignment
        simp
      · exact stripRouteInteriorAssignments_isVertex_false
          period color tailMember

/-- Every flattened strip route assignment is a nonvertex cell. -/
theorem PlanarPresentation.finalStripRouteAssignment_isVertex_false
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {assignment : NormalizedCellAssignment}
    (member : assignment ∈ presentation.finalStripRouteAssignments) :
    assignment.2.isVertex = false := by
  simp only [PlanarPresentation.finalStripRouteAssignments,
    List.mem_flatMap] at member
  rcases member with ⟨edge, _, assignmentMember⟩
  exact stripRouteInteriorAssignments_isVertex_false _ _ assignmentMember

/-- A strip lookup result classified as a vertex comes from a listed
normalized vertex center. -/
theorem PlanarPresentation.exists_vertex_of_finalStripCellTypeAt_isVertex
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {location : Cell}
    (isVertex : (presentation.finalStripCellTypeAt location).isVertex = true) :
    ∃ vertex ∈ problem.contractedGraph.vertices,
      location = stripRasterLocation presentation.finalNormalizationPeriod
        (presentation.finalNormalizationPosition vertex) := by
  unfold PlanarPresentation.finalStripCellTypeAt at isVertex
  generalize lookupEqual :
      presentation.finalStripCellAssignments.lookup location = result at isVertex
  cases result with
  | none => simp [OrthogonalCellType.isVertex] at isVertex
  | some cellType =>
      simp only [Option.getD_some] at isVertex
      have assignmentMember : (location, cellType) ∈
          presentation.finalStripCellAssignments :=
        List.mem_of_lookup_eq_some lookupEqual
      simp only [PlanarPresentation.finalStripCellAssignments,
        List.mem_append] at assignmentMember
      rcases assignmentMember with vertexMember | routeMember
      · simp only [PlanarPresentation.finalStripVertexAssignments,
          List.mem_map] at vertexMember
        rcases vertexMember with ⟨vertex, vertexListed, assignmentEqual⟩
        exact ⟨vertex, vertexListed,
          (congrArg Prod.fst assignmentEqual).symm⟩
      · have routeNonvertex :=
          presentation.finalStripRouteAssignment_isVertex_false routeMember
        rw [routeNonvertex] at isVertex
        contradiction

/-- The compiled rectangular strip has at least one nonvertex cell between
every pair of degree-three vertex cells. -/
theorem PlanarPresentation.stripNormalizedOrthogonalDrawing_verticesSeparated
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.stripNormalizedOrthogonalDrawing.VerticesSeparated := by
  apply presentation.stripNormalizedOrthogonalDrawing_verticesSeparated_of_lookup
  intro position side currentIsVertex
  rcases presentation.exists_vertex_of_finalStripCellTypeAt_isVertex
      currentIsVertex with
    ⟨currentVertex, currentMember, currentEqual⟩
  have currentAssignmentMember :
      (stripRasterLocation presentation.finalNormalizationPeriod
          (presentation.finalNormalizationPosition currentVertex),
        presentation.finalVertexCellType currentVertex) ∈
        presentation.finalStripVertexAssignments := by
    exact List.mem_map.mpr ⟨currentVertex, currentMember, rfl⟩
  have currentInterior :=
    presentation.finalStripVertexAssignment_vertical_interior
      currentAssignmentMember
  by_contra neighborNotFalse
  have neighborIsVertex :
      (presentation.finalStripCellTypeAt
        (((presentation.stripNormalizedOrthogonalDrawing.neighbor
            position side).1.val : Int),
          ((presentation.stripNormalizedOrthogonalDrawing.neighbor
            position side).2.val : Int))).isVertex = true := by
    cases value : (presentation.finalStripCellTypeAt
      (((presentation.stripNormalizedOrthogonalDrawing.neighbor
          position side).1.val : Int),
        ((presentation.stripNormalizedOrthogonalDrawing.neighbor
          position side).2.val : Int))).isVertex <;> simp_all
  rcases presentation.exists_vertex_of_finalStripCellTypeAt_isVertex
      neighborIsVertex with
    ⟨neighborVertex, neighborMember, neighborEqual⟩
  have neighborValues :=
    presentation.stripNeighbor_values_eq_raster_add_side_step position
      (presentation.finalNormalizationPosition currentVertex) side
      currentInterior currentEqual
  have stripEqual := neighborEqual.symm.trans neighborValues
  have rasterEqual :=
    rasterLocation_eq_of_stripRasterLocation_eq stripEqual
  exact presentation.rasterized_finalNormalizationPositions_not_unitStep
    currentVertex neighborVertex (axisDirectionOfSide side)
      (axisDirectionOfSide_isGenuine side) rasterEqual

end PeriodicThreeDM
end LeanTrominoes
