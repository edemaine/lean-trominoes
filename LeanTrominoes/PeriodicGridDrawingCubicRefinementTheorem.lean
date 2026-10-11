/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendContractionPlanarity
import LeanTrominoes.PeriodicGridDrawingRawBendContractionLocality

/-! # Theorem 2.2: cubic orthogonal refinement of planar local polygonal drawings

The period is at most `84480*M^3`. Original vertex positions are multiplied
by `(16*M+32)*(160*M+1600)` exactly. Loops and bends on periodic seams are
included; no straight-input hypothesis is required.
-/
namespace LeanTrominoes.PeriodicGridDrawing
open RawBendSubdivision

theorem polygonal_cubic_refinement {V : Type*} [DecidableEq V]
    {graph : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal) (drawingLocal : drawing.IsRealLocal graph) :
    ∃ output : PeriodicGridDrawing, output.IsRealPlanarDrawing graph ∧ output.IsRealLocal graph ∧
      output.IsOrthogonal ∧ output.gridSize≤84480*drawing.gridSize^3 ∧
      output.vertexPositions=drawing.vertexPositions.map (Cell.scale (cubicFactor drawing)) := by
  exact ⟨contractedDrawing graph drawing,
    contractedDrawing_planar planar drawingLocal graphLocal degree,
    contractedDrawing_local planar drawingLocal graphLocal degree,
    contractedDrawing_orthogonal planar degree,
    contractedDrawing_gridSize_bound graph drawing,rfl⟩

end LeanTrominoes.PeriodicGridDrawing
