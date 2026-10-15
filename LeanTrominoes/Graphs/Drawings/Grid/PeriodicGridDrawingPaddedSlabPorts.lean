/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingSeamPortLocality
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedPeriodicColumnRefinement
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundaryMatchingCorrect

/-! # Crossing ports satisfy the bounded-depth rectangle router's margins -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

def paddedSlabWidth (drawing : PeriodicGridDrawing) : Int :=
  paddedRefinementFactor drawing.gridSize-10*crossingBound drawing.gridSize

def paddedSlabOrigin (drawing : PeriodicGridDrawing) (column row : Int) : Cell :=
  ((paddedRefinementFactor drawing.gridSize : Int)*column+5*crossingBound drawing.gridSize,
    (paddedGridSize drawing.gridSize : Int)*row)

def paddedVerticalSlabPort {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (height : ℚ) (row : Int) (right : Bool) : Port :=
  ⟨if right then 2 else 0,paddedPeriodicColumnHeight graph drawing line height-(paddedGridSize drawing.gridSize : Int)*row⟩

def paddedHorizontalSlabPort {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (abscissa : ℚ) (top : Bool) : Port :=
  ⟨if top then 1 else 3,periodicSeamCoordinate graph drawing abscissa-
    (paddedRefinementFactor drawing.gridSize : Int)*periodicSeamSlab graph drawing abscissa-5*crossingBound drawing.gridSize⟩

theorem paddedSlab_room (drawing : PeriodicGridDrawing) :
    2*(2*(crossingBound drawing.gridSize : Int)) < drawing.paddedSlabWidth ∧
      2*(2*(crossingBound drawing.gridSize : Int)) < paddedGridSize drawing.gridSize := by
  have widthRoom : 4*(crossingBound drawing.gridSize : Int) <
      (paddedRefinementFactor drawing.gridSize : Int)-10*crossingBound drawing.gridSize := by
    simpa only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
      padded_slab_room (crossingBound drawing.gridSize)
  have gridPositive : (1 : Int) ≤ drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have factorPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have factorRoom : 4*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    omega
  simp only [paddedSlabWidth,paddedGridSize,Nat.cast_mul]
  constructor
  · omega
  · nlinarith

theorem paddedVerticalSlabPort_inside {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) {line : Int}
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line) (right : Bool) :
    let height := (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line
    (paddedVerticalSlabPort graph drawing line height (rationalCell drawing.gridSize height) right).Inside
      drawing.paddedSlabWidth (paddedGridSize drawing.gridSize) (2*crossingBound drawing.gridSize) := by
  have bounds := paddedPeriodicColumnHeight_row_clearance compatible degree member straight edgeLocal cell crosses
  dsimp only at bounds
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  cases right <;> simp [paddedVerticalSlabPort,Port.Inside]
  all_goals constructor <;> nlinarith [bounds.1,bounds.2]

theorem paddedHorizontalSlabPort_inside {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    {abscissa : ℚ} (member : rationalResidue drawing.gridSize abscissa ∈ seamCrossingAbscissae graph drawing 0) (top : Bool) :
    (paddedHorizontalSlabPort graph drawing abscissa top).Inside
      drawing.paddedSlabWidth (paddedGridSize drawing.gridSize) (2*crossingBound drawing.gridSize) := by
  have bounds := periodicSeamCoordinate_slab_clearance compatible degree member
  cases top <;> simp [paddedHorizontalSlabPort,Port.Inside,paddedSlabWidth]
  all_goals constructor <;> nlinarith [bounds.1,bounds.2]

theorem paddedVerticalSlabPort_point {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column row : Int) (height : ℚ) (right : Bool) :
    Cell.add (drawing.paddedSlabOrigin column row)
      ((paddedVerticalSlabPort graph drawing (column+if right then 1 else 0) height row right).point
        drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)) =
      ((paddedRefinementFactor drawing.gridSize : Int)*(column+if right then 1 else 0)+
        (if right then -5 else 5)*crossingBound drawing.gridSize,
        paddedPeriodicColumnHeight graph drawing (column+if right then 1 else 0) height) := by
  cases right <;> apply Prod.ext <;>
    simp [paddedSlabOrigin,paddedVerticalSlabPort,Port.point,paddedSlabWidth,Cell.add] <;> ring

theorem paddedHorizontalSlabPort_point {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (abscissa : ℚ) (row : Int) (top : Bool) :
    Cell.add (drawing.paddedSlabOrigin (periodicSeamSlab graph drawing abscissa) row)
      ((paddedHorizontalSlabPort graph drawing abscissa top).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)) =
      (periodicSeamCoordinate graph drawing abscissa,(paddedGridSize drawing.gridSize : Int)*(row+if top then 1 else 0)) := by
  cases top <;> apply Prod.ext <;>
    simp [paddedSlabOrigin,paddedHorizontalSlabPort,Port.point,Cell.add] <;> ring

end LeanTrominoes.PeriodicGridDrawing
