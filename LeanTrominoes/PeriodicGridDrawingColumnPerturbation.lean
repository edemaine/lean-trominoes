/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVirtualRowClearance
import LeanTrominoes.PeriodicGridDrawingVirtualSlabCuts
import LeanTrominoes.GridSegmentRationalVerticalPerturbation

/-! # One rational column-cut width preserves crossing and incidence orders -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalPerturbation

def columnCrossingValues {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : List (ℚ × ℚ) :=
  (List.range drawing.gridSize).flatMap fun (column : Nat) =>
    (verticalCrossingCopies graph drawing (column : Int)).flatMap fun key =>
      [((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column,
          (drawing.liftedStraightSegment key.1 key.2).rationalSlope),
        ((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column,
          -(drawing.liftedStraightSegment key.1 key.2).rationalSlope)]

def columnIncidenceValues {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : List (ℚ × ℚ) :=
  graph.edges.zipIdx.flatMap fun tagged =>
    [(((drawing.outwardStraightSegment tagged false).start.2 : ℚ),(drawing.outwardStraightSegment tagged false).rationalSlope),
      (((drawing.outwardStraightSegment tagged false).start.2 : ℚ),-(drawing.outwardStraightSegment tagged false).rationalSlope),
      (((drawing.outwardStraightSegment tagged true).start.2 : ℚ),(drawing.outwardStraightSegment tagged true).rationalSlope),
      (((drawing.outwardStraightSegment tagged true).start.2 : ℚ),-(drawing.outwardStraightSegment tagged true).rationalSlope)]

def columnPerturbationValues {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : List (ℚ × ℚ) :=
  (columnCrossingValues graph drawing ++ columnIncidenceValues graph drawing) ++
    [(-seamPerturbation graph drawing,0),((drawing.gridSize : ℚ)-seamPerturbation graph drawing,0)]

def columnPerturbation {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : ℚ :=
  min (columnCutMargin graph drawing) (margin (columnPerturbationValues graph drawing))/2

theorem mem_columnPerturbationValues_crossing {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {column : Nat} (columnBound : column < drawing.gridSize) {key : Nat × Cell}
    (member : key ∈ verticalCrossingCopies graph drawing column) (negative : Bool) :
    ((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column,
      if negative then -(drawing.liftedStraightSegment key.1 key.2).rationalSlope else
        (drawing.liftedStraightSegment key.1 key.2).rationalSlope) ∈ columnPerturbationValues graph drawing := by
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  exact List.mem_flatMap.mpr ⟨column,List.mem_range.mpr columnBound,List.mem_flatMap.mpr ⟨key,member,by cases negative <;> simp⟩⟩

theorem mem_columnPerturbationValues_incidence {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target negative : Bool) :
    (((drawing.outwardStraightSegment tagged target).start.2 : ℚ),
      if negative then -(drawing.outwardStraightSegment tagged target).rationalSlope else
        (drawing.outwardStraightSegment tagged target).rationalSlope) ∈ columnPerturbationValues graph drawing := by
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨tagged,member,by cases target <;> cases negative <;> simp⟩

theorem mem_columnPerturbationValues_rows {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) :
    (-seamPerturbation graph drawing,0) ∈ columnPerturbationValues graph drawing ∧
      ((drawing.gridSize : ℚ)-seamPerturbation graph drawing,0) ∈ columnPerturbationValues graph drawing := by
  constructor <;> apply List.mem_append.mpr <;> right <;> simp

theorem columnPerturbation_positive {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    0 < columnPerturbation graph drawing :=
  div_pos (lt_min (columnCutMargin_positive planar straight) (margin_positive _)) (by norm_num)

theorem columnPerturbation_le_cutMargin {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    columnPerturbation graph drawing ≤ columnCutMargin graph drawing := by
  have positive := columnPerturbation_positive planar straight
  have bound := min_le_left (columnCutMargin graph drawing) (margin (columnPerturbationValues graph drawing))
  unfold columnPerturbation at positive ⊢
  linarith

theorem columnPerturbation_le_margin {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    columnPerturbation graph drawing ≤ margin (columnPerturbationValues graph drawing) := by
  have positive := columnPerturbation_positive planar straight
  have bound := min_le_right (columnCutMargin graph drawing) (margin (columnPerturbationValues graph drawing))
  unfold columnPerturbation at positive ⊢
  linarith

theorem columnPerturbation_preserves_order {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : ℚ × ℚ} (firstMember : first ∈ columnPerturbationValues graph drawing)
    (secondMember : second ∈ columnPerturbationValues graph drawing) (ordered : Before first second) :
    evaluate (columnPerturbation graph drawing) first < evaluate (columnPerturbation graph drawing) second :=
  evaluate_order (columnPerturbation_positive planar straight) (columnPerturbation_le_margin planar straight) firstMember secondMember ordered

end LeanTrominoes.PeriodicGridDrawing
