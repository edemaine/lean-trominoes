/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleRoutePlacement

/-! # Periodic rectangle routes meet other rectangles only at their endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting PeriodicOrthocrossing

theorem rectangleRouteIndex_injective {drawing : PeriodicGridDrawing} {firstColumn lastColumn : Nat}
    (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize) {firstCell lastCell : Cell}
    (equal : drawing.rectangleRouteIndex firstColumn firstCell = drawing.rectangleRouteIndex lastColumn lastCell) :
    (firstColumn,firstCell) = (lastColumn,lastCell) := by
  have xEqual := congrArg Prod.fst equal
  have yEqual := congrArg Prod.snd equal
  dsimp only [rectangleRouteIndex] at xEqual yEqual
  have modulus := congrArg (fun value : Int => value % (drawing.gridSize : Int)) xEqual
  simp only [Int.add_mul_emod_self_left] at modulus
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast firstBound),
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast lastBound)] at modulus
  have columnsEqual : firstColumn = lastColumn := by exact_mod_cast modulus
  subst lastColumn
  have gridPositive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have cellsX : firstCell.1 = lastCell.1 := by nlinarith [xEqual]
  exact Prod.ext rfl (Prod.ext cellsX yEqual)

theorem rectangleChordFamily_padded_margin {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) :
    chord.1.Inside drawing.paddedSlabWidth (paddedGridSize drawing.gridSize) (2*crossingBound drawing.gridSize) ∧
      chord.2.Inside drawing.paddedSlabWidth (paddedGridSize drawing.gridSize) (2*crossingBound drawing.gridSize) := by
  obtain ⟨parent,_,first,last,lookup,rfl⟩ := rectangleChordFamily_sources member
  have data := rectangleParentChord_data graph drawing column parent lookup
  exact ⟨rectanglePort_integral_inside planar degree graphLocal straight column data.1,
    rectanglePort_integral_inside planar degree graphLocal straight column data.2.1⟩

theorem liftedRectangleInputRoutes_distinct_cells_contact_endpoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {firstColumn lastColumn : Nat} (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize)
    {first last : Chord} (firstMember : first ∈ rectangleChordFamily graph drawing firstColumn)
    (lastMember : last ∈ rectangleChordFamily graph drawing lastColumn) (firstCell lastCell : Cell)
    (different : (firstColumn,firstCell) ≠ (lastColumn,lastCell)) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing firstColumn firstCell first) point)
    (lastContains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing lastColumn lastCell last) point) :
    GridPolyline.RealIsEndpoint (liftedRectangleInputRoute graph drawing firstColumn firstCell first) point := by
  have firstInside := rectangleChordFamily_padded_margin planar degree graphLocal straight firstMember
  have lastInside := rectangleChordFamily_padded_margin planar degree graphLocal straight lastMember
  have radiusPositive : (0 : Int) < crossingBound drawing.gridSize := by
    have positive : 0 < drawing.gridSize := Nat.zero_lt_succ drawing.gridSizePred
    unfold crossingBound
    positivity
  have pitchPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have stripGap : drawing.paddedSlabWidth < (paddedRefinementFactor drawing.gridSize : Int) := by unfold paddedSlabWidth; omega
  have firstDepth : (matchingDepth (rectangleChordFamily graph drawing firstColumn) first : Int) ≤ 2*crossingBound drawing.gridSize := by
    have depth := matchingDepth_le_card firstMember
    have card := rectangleChordFamily_card_bound planar.1.1 degree firstColumn
    exact_mod_cast (by omega : matchingDepth (rectangleChordFamily graph drawing firstColumn) first ≤ 2*crossingBound drawing.gridSize)
  have lastDepth : (matchingDepth (rectangleChordFamily graph drawing lastColumn) last : Int) ≤ 2*crossingBound drawing.gridSize := by
    have depth := matchingDepth_le_card lastMember
    have card := rectangleChordFamily_card_bound planar.1.1 degree lastColumn
    exact_mod_cast (by omega : matchingDepth (rectangleChordFamily graph drawing lastColumn) last ≤ 2*crossingBound drawing.gridSize)
  have indicesDifferent : drawing.rectangleRouteIndex firstColumn firstCell ≠ drawing.rectangleRouteIndex lastColumn lastCell :=
    fun equal => different (rectangleRouteIndex_injective firstBound lastBound equal)
  unfold liftedRectangleInputRoute rectangleInputRoute matchingRoute at firstContains lastContains ⊢
  rw [rectangleRouteOffset_eq_slabOffset] at firstContains lastContains ⊢
  exact distinct_slabs_contact_first_endpoint pitchPositive stripGap
    (by exact_mod_cast matchingDepth_positive (rectangleChordFamily graph drawing firstColumn) first)
    (by exact_mod_cast matchingDepth_positive (rectangleChordFamily graph drawing lastColumn) last)
    firstDepth lastDepth (paddedSlab_room drawing) firstInside.1 firstInside.2 lastInside.1 lastInside.2
    (rectangleChordFamily_valid planar degree graphLocal straight firstMember).2.2 indicesDifferent firstContains lastContains

theorem liftedRectangleInputRoutes_same_cell_disjoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {first last : Chord} (firstMember : first ∈ rectangleChordFamily graph drawing column)
    (lastMember : last ∈ rectangleChordFamily graph drawing column) (different : first ≠ last) (cell : Cell) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell first) point)
    (lastContains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell last) point) : False :=
  rectangleInputRoutes_disjoint planar degree graphLocal straight firstMember lastMember different
    ((GridPolyline.realContains_translate_inverse _ _ _).mp firstContains) ((GridPolyline.realContains_translate_inverse _ _ _).mp lastContains)

end LeanTrominoes.PeriodicGridDrawing
