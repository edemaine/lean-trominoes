/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleRouteContactParents
import LeanTrominoes.PeriodicGridDrawingRectangleExternalContacts

/-! # A rectangle contact with a crossing strip recovers a vertical parent port -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem liftedRectangleParentRoute_strip_contact_key {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) (parent : Nat × Cell)
    {keys : RectanglePortKey Vertex × RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some keys) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell
      (keys.1.integralPort graph drawing column,keys.2.integralPort graph drawing column)) point)
    (line : Int)
    (strip : |point.1-(paddedRefinementFactor drawing.gridSize : ℝ)*line| ≤ 5*(crossingBound drawing.gridSize : ℝ)) :
    ∃ right raw, (RectanglePortKey.vertical right raw).Valid graph drawing column ∧
      (RectanglePortKey.vertical right raw).parentKey = parent ∧
      point = realCell (rectangleLiftedPortPoint graph drawing column cell (.vertical right raw)) ∧
      line = ((column+if right then 1 else 0 : Nat) : Int)+(drawing.gridSize : Int)*cell.1 := by
  have chordMember := rectangleParentChord_mem_family planar.1.1 graphLocal straight column parent lookup
  have endpoint := liftedRectangleInputRoute_column_strip_contact_endpoint planar degree graphLocal straight chordMember cell contains line strip
  obtain ⟨key,valid,keyParent,pointEq⟩ := liftedRectangleParentRoute_endpoint_key column cell parent lookup endpoint
  have contact := liftedRectangleInputRoute_column_strip_contact planar degree graphLocal straight chordMember cell contains line strip
  rcases contact with ⟨lineEq,atLeft⟩ | ⟨lineEq,atRight⟩
  · have face : (rectangleLiftedPortPoint graph drawing column cell key).1 =
        (drawing.rectangleRouteOffset column cell).1+0 := by
      have x := congrArg Prod.fst pointEq
      simp only [realCell] at x
      have faceReal : ((rectangleLiftedPortPoint graph drawing column cell key).1 : ℝ) =
          (drawing.rectangleRouteOffset column cell).1+0 := by
        simp only [rectangleRouteOffset,paddedSlabOrigin]
        push_cast
        linarith only [x,atLeft]
      exact_mod_cast faceReal
    obtain ⟨raw,rfl⟩ := rectanglePort_vertical_of_integral_face planar degree graphLocal straight column cell false valid face
    refine ⟨false,raw,valid,keyParent,pointEq,?_⟩
    simpa only [Bool.false_eq_true,if_false,Nat.add_zero,rectangleRouteIndex] using lineEq
  · have face : (rectangleLiftedPortPoint graph drawing column cell key).1 =
        (drawing.rectangleRouteOffset column cell).1+drawing.paddedSlabWidth := by
      have x := congrArg Prod.fst pointEq
      simp only [realCell] at x
      have faceReal : ((rectangleLiftedPortPoint graph drawing column cell key).1 : ℝ) =
          (drawing.rectangleRouteOffset column cell).1+drawing.paddedSlabWidth := by
        simp only [rectangleRouteOffset,paddedSlabOrigin,paddedSlabWidth]
        push_cast at atRight ⊢
        linarith only [x,atRight]
      exact_mod_cast faceReal
    obtain ⟨raw,rfl⟩ := rectanglePort_vertical_of_integral_face planar degree graphLocal straight column cell true valid face
    refine ⟨true,raw,valid,keyParent,pointEq,?_⟩
    simpa [rectangleRouteIndex,add_comm,add_left_comm,add_assoc] using lineEq

end LeanTrominoes.PeriodicGridDrawing
