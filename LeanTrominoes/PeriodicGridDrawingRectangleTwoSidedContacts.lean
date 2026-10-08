/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleExternalContacts
import LeanTrominoes.OrthogonalVertexEnlargedBoundaryContacts

/-! # Rectangle joins occur at endpoints of both participating route pieces -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem crossing_bar_rectangle_contact_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : OrthogonalBoundaryRouting.Chord} (member : chord ∈ rectangleChordFamily graph drawing column)
    (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point) (line ordinate : Int)
    (barContains : GridPolyline.RealContains
      (enlargedCrossingBar (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize) line ordinate) point) :
    GridPolyline.RealIsEndpoint (liftedRectangleInputRoute graph drawing column cell chord) point ∧
      GridPolyline.RealIsEndpoint
        (enlargedCrossingBar (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize) line ordinate) point := by
  refine ⟨liftedRectangleInputRoute_crossing_bar_contact_endpoint planar degree graphLocal straight member cell contains line ordinate barContains,?_⟩
  have bounds := enlargedCrossingBar_real_bounds _ _ _ _ barContains
  have boundary := liftedRectangleInputRoute_column_strip_contact_strip_boundary planar degree graphLocal straight member cell contains line bounds.1
  rcases boundary with left | right
  · refine Or.inl ⟨((paddedRefinementFactor drawing.gridSize : Int)*line-5*crossingBound drawing.gridSize,ordinate),by simp [enlargedCrossingBar],?_⟩
    apply Prod.ext
    · simp only [realCell,Prod.fst,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
      linarith
    · exact bounds.2
  · refine Or.inr ⟨((paddedRefinementFactor drawing.gridSize : Int)*line+5*crossingBound drawing.gridSize,ordinate),by simp [enlargedCrossingBar],?_⟩
    apply Prod.ext
    · simp only [realCell,Prod.fst,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
      linarith
    · exact bounds.2

theorem vertex_fan_rectangle_contact_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : OrthogonalBoundaryRouting.Chord} (member : chord ∈ rectangleChordFamily graph drawing column)
    (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point)
    (position : Cell) (profile : AnchorProfile) (index : Fin 4) (profileDegree : profile.degree ≤ 4) (valid : index.val < profile.degree)
    (fanContains : GridPolyline.RealContains
      (enlargedRectangleTemplate (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize) position profile index) point) :
    GridPolyline.RealIsEndpoint (liftedRectangleInputRoute graph drawing column cell chord) point ∧
      GridPolyline.RealIsEndpoint
        (enlargedRectangleTemplate (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize) position profile index) point := by
  refine ⟨liftedRectangleInputRoute_vertex_fan_contact_endpoint planar degree graphLocal straight member cell contains position profile index fanContains,?_⟩
  exact enlargedRectangleTemplate_vertical_boundary_contact_endpoint _ (crossingBound_positive drawing) position profile index profileDegree valid fanContains
    (liftedRectangleInputRoute_column_strip_contact_strip_boundary planar degree graphLocal straight member cell contains position.1
      (enlargedRectangleTemplate_real_bounds _ _ _ _ _ fanContains).1)

end LeanTrominoes.PeriodicGridDrawing
