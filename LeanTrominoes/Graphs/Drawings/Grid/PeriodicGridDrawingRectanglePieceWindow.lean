/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceEnumeration
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleParameterCoverage

/-! # The executable rectangle-piece list exhausts every retained clip -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing RationalAffineBoundary RationalIntervalPartition

theorem rectangleEdgePiece_mem {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (columnBound : column < drawing.gridSize) (cell : Cell)
    {piece : EdgeRoutePiece} (lookup : rectangleEdgePiece? graph drawing index column cell = some piece) :
    piece ∈ rectangleEdgePieces graph drawing index := by
  have cellMember : cell ∈ neighborTranslations := by
    cases chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) with
    | none => simp [rectangleEdgePiece?,chord] at lookup
    | some keys =>
      have data := rectangleParentChord_data graph drawing column (index,Cell.scale (-1) cell) chord
      have parentMember := rectanglePort_parent_mem_nineEdgeCopies compatible graphLocal straight data.1
      rw [data.2.2.1] at parentMember
      obtain ⟨_,_,_,negativeMember⟩ := mem_nineEdgeCopies.mp parentMember
      have neighbor := (mem_neighborTranslations_iff _).mp negativeMember
      apply (mem_neighborTranslations_iff cell).mpr
      simp only [IsNeighborTranslation,Cell.scale,neg_one_mul] at neighbor ⊢
      constructor <;> omega
  exact List.mem_flatMap.mpr ⟨column,List.mem_range.mpr columnBound,
    List.mem_filterMap.mpr ⟨cell,cellMember,lookup⟩⟩

theorem rectangleEdgePieces_cover_clip {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (columnBound : column < drawing.gridSize) (cell : Cell)
    {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) = some (first,last))
    {point : ℚ × ℚ}
    (inside : ClosedPoint (1-2*columnPerturbation graph drawing) drawing.gridSize
      (rectangleAffineBase graph drawing column (index,Cell.scale (-1) cell))
      (drawing.liftedStraightSegment index (Cell.scale (-1) cell)).rationalSlope point) :
    ∃ piece ∈ rectangleEdgePieces graph drawing index,
      piece.start ≤ (drawing.liftedStraightSegment index (Cell.scale (-1) cell)).rationalXParameter
          ((column : ℚ)+columnPerturbation graph drawing+point.1) ∧
        (drawing.liftedStraightSegment index (Cell.scale (-1) cell)).rationalXParameter
          ((column : ℚ)+columnPerturbation graph drawing+point.1) ≤ piece.finish := by
  let piece : EdgeRoutePiece :=
    { start := min (rectanglePortParentParameter graph drawing column (index,Cell.scale (-1) cell) first)
        (rectanglePortParentParameter graph drawing column (index,Cell.scale (-1) cell) last)
      finish := max (rectanglePortParentParameter graph drawing column (index,Cell.scale (-1) cell) first)
        (rectanglePortParentParameter graph drawing column (index,Cell.scale (-1) cell) last)
      route := translatePolyline (drawing.rectangleRouteOffset column cell)
        (orientedRectangleInputRoute graph drawing column (index,Cell.scale (-1) cell) first last) }
  have pieceLookup : rectangleEdgePiece? graph drawing index column cell = some piece := by
    simp only [rectangleEdgePiece?,lookup,Option.map_some]
    rfl
  refine ⟨piece,rectangleEdgePiece_mem planar.1.1 graphLocal straight index column columnBound cell pieceLookup,?_⟩
  exact (rectangleParentChordInterval_contains_iff planar graphLocal straight column columnBound
    (index,Cell.scale (-1) cell) lookup inside.1).mpr inside

end LeanTrominoes.PeriodicGridDrawing
