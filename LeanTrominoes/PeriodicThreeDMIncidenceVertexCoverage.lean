/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceVertexCoverage
import LeanTrominoes.PeriodicThreeDMGraph

/-!
# Endpoint coverage for periodic 3DM incidence drawings

Every triple prototype has its three colored incidence edges.  Under the
degree-two-or-three promise, every declared colored element also occurs in an
incidence.  Thus every graph vertex is incident, and any compatible drawing
with nondegenerate edge routes covers all stored vertex positions by lifted
segment endpoints.
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- Periodic 3DM incidence edges always cross the triple/element
bipartition, so no protoedge is a loop. -/
theorem incidenceGraph_edgesAreLoopless
    (problem : PeriodicThreeDM) :
    PeriodicGridDrawing.EdgesAreLoopless problem.incidenceGraph := by
  intro edge edgeMember
  simp only [incidenceGraph, List.mem_flatMap] at edgeMember
  rcases edgeMember with
    ⟨taggedTriple, taggedMember, edgeMember⟩
  simp only [tripleIncidenceEdges, List.mem_map] at edgeMember
  rcases edgeMember with ⟨color, colorMember, rfl⟩
  intro equal
  cases equal

/-- Degree two or three ensures that every listed triple or colored element
vertex occurs at an edge end. -/
theorem incidenceGraph_everyVertexIncident
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree) :
    PeriodicGridDrawing.EveryVertexIncident problem.incidenceGraph := by
  apply PeriodicGridDrawing.everyVertexIncident_of_mem_incidences
  intro vertex vertexMember
  cases vertex with
  | triple tripleIndex =>
      have indexLt : tripleIndex < problem.triples.length := by
        simpa [incidenceGraph, tripleVertices, elementVertices,
          coloredElementVertices] using vertexMember
      let triple := problem.triples[tripleIndex]'indexLt
      let edge := incidenceEdge tripleIndex triple .red
      have taggedTripleMember :
          (triple, tripleIndex) ∈ problem.triples.zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?,
          List.getElem?_eq_some_iff]
        exact ⟨indexLt, rfl⟩
      have edgeMember : edge ∈ problem.incidenceGraph.edges := by
        unfold incidenceGraph
        apply List.mem_flatMap.mpr
        refine ⟨(triple, tripleIndex), taggedTripleMember, ?_⟩
        simp [tripleIncidenceEdges, incidenceColors, edge]
      unfold PeriodicGraph.incidences
      apply List.mem_flatMap.mpr
      refine ⟨edge, edgeMember, ?_⟩
      simp [edge, incidenceEdge, PeriodicEdge.incidences]
  | element color atom =>
      have atomLt : atom < problem.elementCount color := by
        cases color <;>
          simpa [incidenceGraph, tripleVertices, elementVertices,
            coloredElementVertices] using vertexMember
      have degreeMem := degree color atom atomLt
      have degreePositive : 0 < problem.degree color atom := by
        simp at degreeMem
        omega
      apply List.count_pos_iff.mp
      rw [incidenceGraph_element_degree]
      exact degreePositive

/-- A compatible drawing of a degree-two-or-three periodic 3DM incidence
graph covers every stored vertex position by a lifted segment endpoint. -/
theorem incidenceDrawing_vertexPositionsCoveredBySegmentEndpoints
    (problem : PeriodicThreeDM)
    (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible problem.incidenceGraph)
    (degree : problem.DegreeTwoOrThree) :
    drawing.VertexPositionsCoveredBySegmentEndpoints := by
  exact
    PeriodicGridDrawing.vertexPositionsCoveredBySegmentEndpoints_of_compatible
      problem.incidenceGraph drawing compatible
      (incidenceGraph_everyVertexIncident problem degree)
      (PeriodicGridDrawing.edgeRoutesHaveSegments_of_compatible_of_loopless
        problem.incidenceGraph drawing compatible
        (incidenceGraph_edgesAreLoopless problem))

end PeriodicThreeDM
end LeanTrominoes
