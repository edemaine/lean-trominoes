/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendFanRectangleLocality
import LeanTrominoes.PeriodicGridDrawingRawBendPeriodicCores

/-! # Original-vertex fans have an integer margin inside parent rectangles -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem original_position_parent_margin {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible source) {vertex : V} (member : vertex ∈ source.vertices)
    {offset copy : Cell} (allowed : copy = (0,0) ∨ copy = offset) :
    min 0 ((drawing.gridSize : Int)*offset.1) < (Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation copy)).1 ∧
      (Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation copy)).1 < (drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.1) ∧
      min 0 ((drawing.gridSize : Int)*offset.2) < (Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation copy)).2 ∧
      (Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation copy)).2 < (drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.2) := by
  have inside := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem member)
  rcases allowed with zero | shift
  · rw [zero]
    simp only [Cell.add,Cell.scale,periodTranslation,mul_zero,add_zero]
    exact ⟨lt_of_le_of_lt (min_le_left _ _) inside.1,
      by nlinarith [inside.2.1,le_max_left 0 ((drawing.gridSize : Int)*offset.1)],
      lt_of_le_of_lt (min_le_left _ _) inside.2.2.1,
      by nlinarith [inside.2.2.2,le_max_left 0 ((drawing.gridSize : Int)*offset.2)]⟩
  · rw [shift]
    simp only [Cell.add,Cell.scale,periodTranslation]
    exact ⟨by nlinarith [inside.1,min_le_right 0 ((drawing.gridSize : Int)*offset.1)],
      by nlinarith [inside.2.1,le_max_right 0 ((drawing.gridSize : Int)*offset.1)],
      by nlinarith [inside.2.2.1,min_le_right 0 ((drawing.gridSize : Int)*offset.2)],
      by nlinarith [inside.2.2.2,le_max_right 0 ((drawing.gridSize : Int)*offset.2)]⟩

theorem original_fanRoute_inside_parent_rectangle {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {port : GraphPort (Vertex V)}
    (portMember : port ∈ allPorts (subdivisionGraph source drawing)) {vertex : V} (original : port.vertex = .original vertex)
    {offset copy : Cell} (allowed : copy = (0,0) ∨ copy = offset) {point : Cell} (member : point ∈ fanRoute source drawing port) :
    (Cubic.coreFactor drawing.gridSize : Int)*min 0 ((drawing.gridSize : Int)*offset.1) ≤
        (Cubic.coreFactor drawing.gridSize : Int)*(Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation copy)).1+point.1 ∧
      (Cubic.coreFactor drawing.gridSize : Int)*(Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation copy)).1+point.1 ≤
        (Cubic.coreFactor drawing.gridSize : Int)*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.1)) ∧
      (Cubic.coreFactor drawing.gridSize : Int)*min 0 ((drawing.gridSize : Int)*offset.2) ≤
        (Cubic.coreFactor drawing.gridSize : Int)*(Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation copy)).2+point.2 ∧
      (Cubic.coreFactor drawing.gridSize : Int)*(Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation copy)).2+point.2 ≤
        (Cubic.coreFactor drawing.gridSize : Int)*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.2)) := by
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) portMember
  rw [original] at vertexMember
  have margin := original_position_parent_margin planar.1.1 (original_vertex_mem.mp vertexMember) allowed
  apply fanRoute_inside_rectangle planar portMember
    (by have spacing := Cubic.coreFactor_slope_spacing drawing.gridSize; omega)
    ⟨margin.1.le,margin.2.1.le,margin.2.2.1.le,margin.2.2.2.le⟩
  · intro _ _
    exact margin
  · intro boundary
    omega
  · intro boundary
    omega
  · intro boundary
    omega
  · intro boundary
    omega
  · exact member

theorem original_fanAt_inside_parent_rectangle {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {port : GraphPort (Vertex V)}
    (portMember : port ∈ allPorts (subdivisionGraph source drawing)) {vertex : V} (original : port.vertex = .original vertex)
    {offset copy : Cell} (allowed : copy = (0,0) ∨ copy = offset) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
      (Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation copy)) port) point) :
    (cubicScale drawing : ℝ)*(min 0 ((drawing.gridSize : Int)*offset.1) : Int) ≤ point.1 ∧
      point.1 ≤ (cubicScale drawing : ℝ)*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.1) : Int) ∧
      (cubicScale drawing : ℝ)*(min 0 ((drawing.gridSize : Int)*offset.2) : Int) ≤ point.2 ∧
      point.2 ≤ (cubicScale drawing : ℝ)*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.2) : Int) := by
  have bounds := fanAt_real_inside_rectangle (Cubic.rasterFactor drawing.gridSize)
    (fun point member => original_fanRoute_inside_parent_rectangle planar portMember original allowed member) contains
  simpa only [cubicScale,Int.cast_mul,Int.cast_natCast] using bounds

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
