/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightRefinementRoutes
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRefinementPieceTranslations

/-! # Every periodic replacement-route point lies on a fan, rectangle, bar, or vertical core -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement

def RefinementPhysicalContains {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) (shift : Cell) (point : ℝ × ℝ) : Prop :=
  GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2) shift) point ∨
  GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) (Cell.add tagged.1.offset shift)) point ∨
  (∃ column, column < drawing.gridSize ∧ ∃ cell piece,
    rectangleEdgePiece? graph drawing tagged.2 column cell = some piece ∧
      GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift) piece.route) point) ∨
  (∃ line, (drawing.liftedStraightSegment tagged.2 shift).CrossesVerticalLine line ∧
    GridPolyline.RealContains (paddedCrossingRoute graph drawing line (tagged.2,shift)) point) ∨
  ((drawing.liftedStraightSegment tagged.2 (0,0)).start.1 = (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 ∧
    ((drawing.liftedStraightSegment tagged.2 shift).verticalCore (paddedRefinementFactor drawing.gridSize)
      (crossingBound drawing.gridSize)).RealContains point)

theorem straightRefinementRoute_physical_image {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (shift : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift)
      (straightRefinementRoute graph drawing tagged)) point) :
    RefinementPhysicalContains graph drawing tagged shift point := by
  have relative := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have transport : ∀ route : List Cell, GridPolyline.RealContains route
      (point.1-(Cell.scale (paddedGridSize drawing.gridSize) shift).1,
       point.2-(Cell.scale (paddedGridSize drawing.gridSize) shift).2) →
      GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift) route) point :=
    fun route => (GridPolyline.realContains_translate_inverse _ route point).mpr
  have sourceTransport : GridPolyline.RealContains (paddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2))
      (point.1-(Cell.scale (paddedGridSize drawing.gridSize) shift).1,
       point.2-(Cell.scale (paddedGridSize drawing.gridSize) shift).2) →
      GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2) shift) point := by
    intro sourceContains
    rw [liftedPaddedIncidenceRoute_eq_translate]
    exact transport _ sourceContains
  have targetTransport : GridPolyline.RealContains
      ((liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).reverse)
      (point.1-(Cell.scale (paddedGridSize drawing.gridSize) shift).1,
       point.2-(Cell.scale (paddedGridSize drawing.gridSize) shift).2) →
      GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) (Cell.add tagged.1.offset shift)) point := by
    intro targetContains
    rw [liftedPaddedIncidenceRoute_add_cell]
    exact transport _ ((GridPolyline.realContains_reverse _ _).mp targetContains)
  unfold straightRefinementRoute at relative
  split_ifs at relative with vertical
  · obtain ⟨piece,pieceMember,pieceContains⟩ := (verticalFanEdgeRoute_valid planar degree straight member vertical).2.2 _ |>.mp relative
    simp only [verticalFanRouteWord,List.mem_cons,List.not_mem_nil,or_false] at pieceMember
    rcases pieceMember with rfl | rfl | rfl
    · exact Or.inl (sourceTransport pieceContains)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨vertical,(verticalCoreRoute_lifted_image planar degree straight member vertical shift point).mp (transport _ pieceContains)⟩)))
    · exact Or.inr (Or.inl (targetTransport pieceContains))
  · obtain ⟨piece,pieceMember,pieceContains⟩ := (nonverticalEdgeRoute_valid planar degree graphLocal straight member vertical).2.2 _ |>.mp relative
    simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at pieceMember
    rcases pieceMember with ((source | rectangle) | crossing) | target
    · subst piece
      exact Or.inl (sourceTransport pieceContains)
    · obtain ⟨column,columnMember,rectangleMember⟩ := List.mem_flatMap.mp rectangle
      obtain ⟨cell,_,lookup⟩ := List.mem_filterMap.mp rectangleMember
      exact Or.inr (Or.inr (Or.inl ⟨column,List.mem_range.mp columnMember,cell,piece,lookup,transport _ pieceContains⟩))
    · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
      split_ifs at lookup with crosses
      have equal := Option.some.inj lookup
      subst piece
      have raw := (crossingEdgePiece_raw_image graph drawing tagged.2 line _).mp pieceContains
      have barContains := transport _ raw
      have translation := paddedCrossingRoute_add_cell graph drawing line (tagged.2,(0,0)) shift
      simp only [Cell.add,zero_add,Prod.eta] at translation
      rw [← translation] at barContains
      have liftedCrosses : (drawing.liftedStraightSegment tagged.2 shift).CrossesVerticalLine
          (line+(drawing.gridSize : Int)*shift.1) := by
        have translated := (GridSegment.crossesVerticalLine_translate (drawing.liftedStraightSegment tagged.2 (0,0))
          (drawing.periodTranslation shift) line).mpr crosses
        simpa [liftedStraightSegment,GridSegment.translate,Cell.add,periodTranslation,Cell.scale] using translated
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_,liftedCrosses,barContains⟩)))
    · subst piece
      exact Or.inr (Or.inl (targetTransport pieceContains))

end LeanTrominoes.PeriodicGridDrawing
