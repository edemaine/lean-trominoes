/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightRefinementPlanarity
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightRefinementLocality

/-! # Theorem 2.2 for planar periodic drawings with straight protoedges -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem straight_refinement {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    ∃ output : PeriodicGridDrawing, output.IsRealPlanarDrawing graph ∧ output.IsRealLocal graph ∧
      output.IsOrthogonal ∧ output.gridSize ≤ 3300*drawing.gridSize^3 ∧
      output.vertexPositions = drawing.vertexPositions.map (Cell.scale (paddedRefinementFactor drawing.gridSize)) := by
  refine ⟨straightRefinementDrawing graph drawing,
    straightRefinementDrawing_isRealPlanarDrawing planar degree graphLocal straight,
    straightRefinementDrawing_isRealLocal planar degree graphLocal straight,
    straightRefinementDrawing_orthogonal planar degree graphLocal straight,
    straightRefinementDrawing_gridSize_cubic,rfl⟩

end LeanTrominoes.PeriodicGridDrawing
