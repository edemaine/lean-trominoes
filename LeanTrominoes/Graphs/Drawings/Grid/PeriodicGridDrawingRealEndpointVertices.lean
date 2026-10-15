/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVertexCoverage
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRealGeometry

/-! # Real route endpoints are lifted graph vertices -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem real_endpoint_is_lifted_vertex {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible source)
    {tagged : PeriodicEdge V × Nat} (member : tagged∈source.edges.zipIdx) (translate : Cell)
    {p : ℝ × ℝ} (endpoint : GridPolyline.RealIsEndpoint (drawing.realEdgeRoute tagged.2 translate) p) :
    ∃ vertex∈drawing.vertexPositions, ∃ cell : Cell, p=realCell (Cell.add vertex (drawing.periodTranslation cell)) := by
  have endpoints := compatible.2.2.2.2.2 tagged member
  have vertices := compatible.1.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  rcases endpoint with ⟨actual,head,equal⟩ | ⟨actual,last,equal⟩
  · have atHead : (drawing.realEdgeRoute tagged.2 translate).head?=
        some (Cell.add (drawing.periodTranslation translate) (drawing.vertexPosition source tagged.1.source)) := by
      simp only [realEdgeRoute,List.head?_map,endpoints.1,Option.map_some]
    have actualEq := Option.some.inj (head.symm.trans atHead)
    refine ⟨drawing.vertexPosition source tagged.1.source,compatible.vertexPosition_mem vertices.1,translate,?_⟩
    simpa only [actualEq,Cell.add,add_comm] using equal
  · have atLast : (drawing.realEdgeRoute tagged.2 translate).getLast?=
        some (Cell.add (drawing.periodTranslation translate)
          (Cell.add (drawing.vertexPosition source tagged.1.target) (drawing.periodTranslation tagged.1.offset))) := by
      simp only [realEdgeRoute,List.getLast?_map,endpoints.2,Option.map_some]
    have actualEq := Option.some.inj (last.symm.trans atLast)
    refine ⟨drawing.vertexPosition source tagged.1.target,compatible.vertexPosition_mem vertices.2,
      Cell.add translate tagged.1.offset,?_⟩
    rw [equal,actualEq]
    congr 1
    apply Prod.ext <;> simp only [periodTranslation,Cell.add,Cell.scale] <;> ring

end LeanTrominoes.PeriodicGridDrawing
