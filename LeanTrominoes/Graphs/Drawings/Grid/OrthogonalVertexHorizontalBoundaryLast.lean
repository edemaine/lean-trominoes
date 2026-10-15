/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexEnlargedHorizontalBoundaryContacts
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedFanPorts

/-! # A nonzero horizontal boundary contact is the fan's outer endpoint -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicGridDrawing

theorem enlargedRectangleTemplate_horizontal_boundary_contact_last (factor : Int) {radius : Nat} (positive : 0 < radius)
    (position : Cell) (profile : AnchorProfile) (index : Fin 4) (degree : profile.degree ≤ 4) (valid : index.val < profile.degree)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius position profile index) point)
    (boundary : point.2-(factor : ℝ)*position.2 = -10*(radius : ℝ) ∨
      point.2-(factor : ℝ)*position.2 = 10*(radius : ℝ)) :
    point = realCell ((enlargedRectangleTemplate factor radius position profile index).getLast?.getD (0,0)) := by
  have endpoint := enlargedRectangleTemplate_horizontal_boundary_contact_endpoint factor positive position profile index degree valid contains boundary
  rcases endpoint with ⟨value,head,pointEq⟩ | ⟨value,last,pointEq⟩
  · have valueEq := Option.some.inj (head.symm.trans (enlargedRectangleTemplate_head factor radius position profile index))
    rw [valueEq] at pointEq
    have y := congrArg Prod.snd pointEq
    simp only [realCell,Cell.scale,Int.cast_mul] at y
    have radiusPositive : (0 : ℝ) < radius := by exact_mod_cast positive
    rcases boundary with south | north <;> linarith
  · simpa only [last,Option.getD_some] using pointEq

end LeanTrominoes.OrthogonalDrawingRefinement
