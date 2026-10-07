/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralRouteSimple
import LeanTrominoes.PeriodicOrthocrossingGeneralVertexAvoidance
import LeanTrominoes.PeriodicOrthocrossingGeneralLocal

/-! # Theorem 2.1: general local periodic orthocrossing drawings on a linear grid -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

theorem drawing_isRealDrawing {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4) (isLocal : graph.IsLocal) :
    (drawing graph orthogonal).IsRealDrawing graph :=
  ⟨drawing_isCompatible wellFormed orthogonal,
    drawing_realRoutesAreSimple wellFormed orthogonal degree isLocal,
    drawing_realVerticesAvoidRoutes wellFormed orthogonal degree isLocal⟩

theorem local_orthocrossing_drawing {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (isLocal : graph.IsLocal) :
    ∃ output : PeriodicGridDrawing, output.IsRealDrawing graph ∧ output.IsRealLocal graph ∧
      output.IsRealOrthocrossing ∧ output.gridSize ≤ 16*(graph.vertices.length+graph.edges.length+1) ∧
      (0 < graph.vertices.length+graph.edges.length → output.gridSize ≤ 32*(graph.vertices.length+graph.edges.length)) := by
  refine ⟨drawing graph false,drawing_isRealDrawing wellFormed false (by simp) isLocal,
    drawing_isRealLocal wellFormed false isLocal,
    drawing_isRealOrthocrossing wellFormed false (by simp) isLocal,?_,?_⟩
  · simp [drawing_gridSize,drawingGridSize]
  · exact drawing_gridSize_linear graph false

theorem local_orthogonal_orthocrossing_drawing {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (isLocal : graph.IsLocal) (degree : graph.DegreeAtMost 4) :
    ∃ output : PeriodicGridDrawing, output.IsRealDrawing graph ∧ output.IsRealLocal graph ∧
      output.IsRealOrthocrossing ∧ output.IsOrthogonal ∧
      output.gridSize ≤ 16*(graph.vertices.length+graph.edges.length+1) ∧
      (0 < graph.vertices.length+graph.edges.length → output.gridSize ≤ 32*(graph.vertices.length+graph.edges.length)) := by
  refine ⟨drawing graph true,drawing_isRealDrawing wellFormed true (fun _ => degree) isLocal,
    drawing_isRealLocal wellFormed true isLocal,
    drawing_isRealOrthocrossing wellFormed true (fun _ => degree) isLocal,
    drawing_isOrthogonal wellFormed degree isLocal,?_,?_⟩
  · simp [drawing_gridSize,drawingGridSize]
  · exact drawing_gridSize_linear graph true

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
