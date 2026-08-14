/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentGeometry

/-!
# Exact lookup of normalized 3DM strip assignments

Collision freedom makes the rectangular strip's prioritized association list
an exact finite representation of every normalized vertex and route-interior
assignment.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Every listed strip assignment is returned exactly by the strip lookup. -/
theorem PlanarPresentation.finalStripCellTypeAt_eq_of_mem
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree)
    {location : Cell} {cellType : OrthogonalCellType}
    (member : (location, cellType) ∈
      presentation.finalStripCellAssignments) :
    presentation.finalStripCellTypeAt location = cellType := by
  have lookup := List.lookup_eq_some_of_mem_of_nodup_keys member collisionFree
  simp [PlanarPresentation.finalStripCellTypeAt, lookup]

/-- A contracted vertex contributes its advertised strip assignment. -/
theorem PlanarPresentation.finalStripVertexAssignment_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    (stripRasterLocation presentation.finalNormalizationPeriod
        (presentation.finalNormalizationPosition vertex),
      presentation.finalVertexCellType vertex) ∈
      presentation.finalStripCellAssignments := by
  simp only [PlanarPresentation.finalStripCellAssignments, List.mem_append]
  left
  exact List.mem_map.mpr ⟨vertex, member, rfl⟩

/-- Under strip collision freedom, the compiled cell at a contracted vertex
is exactly its advertised degree-three vertex cell. -/
theorem PlanarPresentation.finalStripCellTypeAt_vertex
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.finalStripCellTypeAt
        (stripRasterLocation presentation.finalNormalizationPeriod
          (presentation.finalNormalizationPosition vertex)) =
      presentation.finalVertexCellType vertex :=
  presentation.finalStripCellTypeAt_eq_of_mem collisionFree
    (presentation.finalStripVertexAssignment_mem member)

/-- Every assignment emitted for a listed normalized route interior belongs
to the combined strip assignment list. -/
theorem PlanarPresentation.stripRouteInteriorAssignment_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {assignment : NormalizedCellAssignment}
    (assignmentMember : assignment ∈
      stripRouteInteriorAssignments presentation.finalNormalizationPeriod
        edge.color (presentation.finalNormalizationRoute edge)) :
    assignment ∈ presentation.finalStripCellAssignments := by
  simp only [PlanarPresentation.finalStripCellAssignments, List.mem_append]
  right
  simp only [PlanarPresentation.finalStripRouteAssignments, List.mem_flatMap]
  exact ⟨edge, edgeMember, assignmentMember⟩

/-- Under collision freedom, every strip route-interior assignment is
returned exactly by the compiled lookup. -/
theorem PlanarPresentation.finalStripCellTypeAt_routeInterior
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {location : Cell} {cellType : OrthogonalCellType}
    (assignmentMember : (location, cellType) ∈
      stripRouteInteriorAssignments presentation.finalNormalizationPeriod
        edge.color (presentation.finalNormalizationRoute edge)) :
    presentation.finalStripCellTypeAt location = cellType :=
  presentation.finalStripCellTypeAt_eq_of_mem collisionFree
    (presentation.stripRouteInteriorAssignment_mem
      edgeMember assignmentMember)

end PeriodicThreeDM
end LeanTrominoes
