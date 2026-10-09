/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendContractionPlanarity
import LeanTrominoes.PeriodicGridDrawingBendContractionLocality

/-! # Polynomial orthogonal refinement of arbitrary planar local polygonal drawings -/
namespace LeanTrominoes.PeriodicGridDrawing
open BendSubdivision

theorem polygonal_refinement {V : Type*} [DecidableEq V]
    {graph : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal) (drawingLocal : drawing.IsRealLocal graph) :
    ∃ output : PeriodicGridDrawing, output.IsRealPlanarDrawing graph ∧ output.IsRealLocal graph ∧
      output.IsOrthogonal ∧ output.gridSize≤865075200*drawing.gridSize^6 ∧
      output.vertexPositions=drawing.vertexPositions.map (Cell.scale (polygonalScale drawing)) := by
  exact ⟨contractedDrawing graph drawing,
    contractedDrawing_planar planar drawingLocal graphLocal degree,
    contractedDrawing_local planar drawingLocal graphLocal degree,
    contractedDrawing_orthogonal planar drawingLocal graphLocal degree,
    contractedDrawing_gridSize_bound graph drawing,rfl⟩

end LeanTrominoes.PeriodicGridDrawing
