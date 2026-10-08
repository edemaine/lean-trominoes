/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVerticalCoreFanOccurrenceSeparation
import LeanTrominoes.PeriodicGridDrawingRefinementPieceTranslations
import LeanTrominoes.PeriodicGridDrawingVerticalCrossingSeparation
import LeanTrominoes.PeriodicGridDrawingRectanglePieceOccurrenceSeparation
import LeanTrominoes.PeriodicGridDrawingVerticalRectangleSeparation

/-! # Shortened vertical cores are separated from all other periodic pieces -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem verticalCore_lifted_fan_contact_identifies_endpoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    (edgeCell : Cell) {port : GraphPort Vertex} (portMember : port ∈ allPorts graph) (fanCell : Cell)
    {point : ℝ × ℝ}
    (coreContains : ((drawing.liftedStraightSegment tagged.2 edgeCell).verticalCore
      (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)).RealContains point)
    (fanContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing port fanCell) point) :
    (port = sourcePort tagged.1 tagged.2 ∧ fanCell = edgeCell) ∨
      (port = targetPort tagged.1 tagged.2 ∧ fanCell = Cell.add tagged.1.offset edgeCell) := by
  have coreTranslated := (verticalCoreRoute_lifted_image planar degree straight member vertical edgeCell point).mpr coreContains
  have relativeCore := (GridPolyline.realContains_translate_inverse _ _ _).mp coreTranslated
  let relativeCell := Cell.add fanCell (Cell.scale (-1) edgeCell)
  have recover : Cell.add relativeCell edgeCell = fanCell := by
    apply Prod.ext <;> simp [relativeCell,Cell.add,Cell.scale]
  have translatedFan := liftedPaddedIncidenceRoute_add_cell graph drawing port relativeCell edgeCell
  rw [recover] at translatedFan
  rw [translatedFan] at fanContains
  have relativeFan := (GridPolyline.realContains_translate_inverse _ _ _).mp fanContains
  have contact := verticalCoreRoute_fan_contact_identifies_endpoint planar degree straight member vertical portMember relativeCell relativeCore relativeFan
  rcases contact with ⟨portEq,cellEq⟩ | ⟨portEq,cellEq⟩
  · exact Or.inl ⟨portEq,by rw [cellEq] at recover; simpa [Cell.add] using recover.symm⟩
  · exact Or.inr ⟨portEq,by rw [cellEq] at recover; exact recover.symm⟩

theorem verticalCore_lifted_avoids_rectangle_piece {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (verticalIndex : Nat) (verticalCell : Cell) (vertical : (drawing.liftedStraightSegment verticalIndex verticalCell).IsVertical)
    (index column : Nat) (cell shift : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {point : ℝ × ℝ}
    (coreContains : ((drawing.liftedStraightSegment verticalIndex verticalCell).verticalCore
      (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)).RealContains point)
    (rectangleContains : GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift) piece.route) point) : False := by
  have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have parentContains := GridSegment.verticalCore_realContains_parent vertical spacing coreContains
  have factorPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have scaledVertical : ((drawing.liftedStraightSegment verticalIndex verticalCell).scale (paddedRefinementFactor drawing.gridSize)).IsVertical := by
    refine ⟨by simp [GridSegment.scale,Cell.scale,vertical.1],?_⟩
    simp only [GridSegment.scale,Cell.scale]
    exact fun equal => vertical.2 (mul_left_cancel₀ factorPositive.ne' equal)
  have x := GridSegment.realContains_vertical_x scaledVertical parentContains
  simp only [GridSegment.scale,Cell.scale,Int.cast_mul,Int.cast_natCast] at x
  cases chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) with
  | none => simp [rectangleEdgePiece?,chord] at lookup
  | some keys =>
    have chordMember := rectangleParentChord_mem_family planar.1.1 graphLocal straight column (index,Cell.scale (-1) cell) chord
    exact liftedRectangleInputRoute_avoids_scaled_column planar degree graphLocal straight chordMember (Cell.add cell shift) _
      ((rectangleEdgePiece?_translated_raw_image index column cell shift lookup chord point).mp rectangleContains) x

end LeanTrominoes.PeriodicGridDrawing
