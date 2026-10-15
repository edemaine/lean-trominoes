/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleOriginalPortBounds
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePortJoins

/-! # Ports of one original edge join across adjacent horizontal period cells -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement RationalIntegerStripCover

def rectangleLiftedPortPoint {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (cell : Cell) (key : RectanglePortKey Vertex) : Cell :=
  Cell.add (drawing.rectangleRouteOffset column cell)
    ((key.integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize))

theorem rectangle_horizontal_ports_join_of_parent {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (index column : Nat) (cell : Cell)
    (first last : Nat × Cell)
    (firstParent : (RectanglePortKey.horizontal (Vertex := Vertex) true first).parentKey = (index,Cell.scale (-1) cell))
    (lastParent : (RectanglePortKey.horizontal (Vertex := Vertex) false last).parentKey = (index,Cell.scale (-1) (Cell.add cell (0,1)))) :
    rectangleLiftedPortPoint graph drawing column cell (.horizontal true first) =
      rectangleLiftedPortPoint graph drawing column (Cell.add cell (0,1)) (.horizontal false last) := by
  have keysEqual : first = last := by
    apply Prod.ext
    · have firstIndex := congrArg Prod.fst firstParent
      have lastIndex := congrArg Prod.fst lastParent
      simpa only [RectanglePortKey.parentKey] using firstIndex.trans lastIndex.symm
    · apply Prod.ext
      · have firstX := congrArg (fun parent : Nat × Cell => parent.2.1) firstParent
        have lastX := congrArg (fun parent : Nat × Cell => parent.2.1) lastParent
        simp [RectanglePortKey.parentKey,Cell.add,Cell.scale] at firstX lastX
        omega
      · have firstY := congrArg (fun parent : Nat × Cell => parent.2.2) firstParent
        have lastY := congrArg (fun parent : Nat × Cell => parent.2.2) lastParent
        simp [RectanglePortKey.parentKey,Cell.add,Cell.scale] at firstY lastY
        omega
  subst last
  exact rectangle_horizontal_ports_join graph drawing column first cell

theorem rectangle_ports_join_across_row {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) {first last : RectanglePortKey Vertex}
    (firstValid : first.Valid graph drawing column) (lastValid : last.Valid graph drawing column)
    (firstParent : first.parentKey = (index,Cell.scale (-1) cell))
    (lastParent : last.parentKey = (index,Cell.scale (-1) (Cell.add cell (0,1))))
    (oldPointEqual : rectanglePortOriginalPoint graph drawing column cell first =
      rectanglePortOriginalPoint graph drawing column (Cell.add cell (0,1)) last) :
    rectangleLiftedPortPoint graph drawing column cell first =
      rectangleLiftedPortPoint graph drawing column (Cell.add cell (0,1)) last := by
  have firstBounds := rectanglePortOriginalPoint_bounds planar graphLocal straight column cell firstValid
  have lastBounds := rectanglePortOriginalPoint_bounds planar graphLocal straight column (Cell.add cell (0,1)) lastValid
  have firstTop : (rectanglePortOriginalPoint graph drawing column cell first).2 =
      (drawing.gridSize : ℚ)*((cell.2 : ℚ)+1)-seamPerturbation graph drawing := by
    have lower := lastBounds.2.1
    rw [← oldPointEqual] at lower
    simp only [Cell.add] at lower
    push_cast at lower
    exact le_antisymm firstBounds.2.2 lower
  have lastBottom : (rectanglePortOriginalPoint graph drawing column (Cell.add cell (0,1)) last).2 =
      (drawing.gridSize : ℚ)*(Cell.add cell (0,1)).2-seamPerturbation graph drawing := by
    rw [← oldPointEqual,firstTop]
    simp [Cell.add]
  obtain ⟨firstRaw,firstEqual⟩ := rectanglePort_horizontal_of_top_contact planar graphLocal straight column cell firstValid firstTop
  obtain ⟨lastRaw,lastEqual⟩ := rectanglePort_horizontal_of_bottom_contact planar graphLocal straight column (Cell.add cell (0,1)) lastValid lastBottom
  rw [firstEqual] at firstParent ⊢
  rw [lastEqual] at lastParent ⊢
  exact rectangle_horizontal_ports_join_of_parent graph drawing index column cell firstRaw lastRaw firstParent lastParent

end LeanTrominoes.PeriodicGridDrawing
