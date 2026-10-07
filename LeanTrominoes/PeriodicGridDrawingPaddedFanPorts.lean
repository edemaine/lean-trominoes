/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingPaddedSlabPorts
import LeanTrominoes.OrthogonalVertexEnlargedTemplates

/-! # Enlarged vertex connectors agree with the adjacent slab's boundary ports -/
namespace LeanTrominoes
namespace OrthogonalDrawingRefinement
open PeriodicOrthocrossing

theorem enlargedRectangleTemplate_head (factor : Int) (radius : Nat) (position : Cell) (profile : AnchorProfile) (index : Fin 4) :
    (enlargedRectangleTemplate factor radius position profile index).head? = some (Cell.scale factor position) := by
  simp [enlargedRectangleTemplate,translatePolyline,scalePolyline,rectangleTemplate_head,Cell.add,Cell.scale]

theorem enlargedRectangleTemplate_last_anchor (factor : Int) (radius : Nat) (position : Cell) (profile : AnchorProfile) (index : Fin 4)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree) {anchor : Cell}
    (lookup : profile.anchors[index.val]? = some anchor) :
    (enlargedRectangleTemplate factor radius position profile index).getLast? =
      some (Cell.add (Cell.scale factor position) (Cell.scale radius anchor)) := by
  simp only [enlargedRectangleTemplate,translatePolyline,scalePolyline,List.getLast?_map]
  rw [rectangleTemplate_last profile index degree valid,lookup]
  rfl

end OrthogonalDrawingRefinement
namespace PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

def paddedFanSlabPort (drawing : PeriodicGridDrawing) (position anchor : Cell) (left : Bool) : Port :=
  ⟨if left then 2 else 0,(paddedRefinementFactor drawing.gridSize : Int)*position.2+
    (crossingBound drawing.gridSize : Int)*anchor.2⟩

theorem paddedFanSlabPort_inside {drawing : PeriodicGridDrawing} {position anchor : Cell}
    (vertexBounds : 0 < position.2 ∧ position.2 < drawing.gridSize)
    (anchorBounds : -10 ≤ anchor.2 ∧ anchor.2 ≤ 10) (left : Bool) :
    (drawing.paddedFanSlabPort position anchor left).Inside drawing.paddedSlabWidth
      (paddedGridSize drawing.gridSize) (2*crossingBound drawing.gridSize) := by
  have factorPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have factorRoom : 12*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp [paddedRefinementFactor]
    omega
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  have lo : (paddedRefinementFactor drawing.gridSize : Int) ≤ (paddedRefinementFactor drawing.gridSize : Int)*position.2 := by
    nlinarith [vertexBounds.1]
  have hi : (paddedRefinementFactor drawing.gridSize : Int)*(position.2+1) ≤
      (paddedRefinementFactor drawing.gridSize : Int)*drawing.gridSize := by
    exact mul_le_mul_of_nonneg_left (by omega) factorPositive.le
  have anchorLo := mul_le_mul_of_nonneg_left anchorBounds.1 nonnegative
  have anchorHi := mul_le_mul_of_nonneg_left anchorBounds.2 nonnegative
  cases left <;> simp [paddedFanSlabPort,Port.Inside,paddedGridSize]
  all_goals constructor <;> nlinarith

theorem paddedFanSlabPort_point {drawing : PeriodicGridDrawing} {position anchor : Cell} (left : Bool)
    (anchorX : anchor.1 = if left then -5 else 5) :
    Cell.add (drawing.paddedSlabOrigin (position.1-if left then 1 else 0) 0)
      ((drawing.paddedFanSlabPort position anchor left).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)) =
    Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) position) (Cell.scale (crossingBound drawing.gridSize) anchor) := by
  cases left <;> apply Prod.ext <;>
    simp [paddedSlabOrigin,paddedSlabWidth,paddedFanSlabPort,Port.point,Cell.add,Cell.scale,anchorX] <;> ring

end PeriodicGridDrawing
end LeanTrominoes
