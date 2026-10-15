/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentLocalSeamBounds
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingSeamCrossingCoordinates

/-! # Row-seam ports remain strictly inside the original column cell -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem straight_lifted_segment_endpoints {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (cell : Cell) :
    drawing.liftedStraightSegment tagged.2 cell =
      GridSegment.mk (Cell.add (drawing.vertexPosition graph tagged.1.source) (Cell.scale drawing.gridSize cell))
        (Cell.add (drawing.vertexPosition graph tagged.1.target) (Cell.scale drawing.gridSize (Cell.add cell tagged.1.offset))) := by
  have ends := compatible.2.2.2.2.2 tagged member
  obtain ⟨first,second,routeEq⟩ := List.length_eq_two.mp straight
  have firstEq : first = drawing.vertexPosition graph tagged.1.source := by simpa [routeEq] using ends.1
  have secondEq : second = Cell.add (drawing.vertexPosition graph tagged.1.target) (drawing.periodTranslation tagged.1.offset) := by
    simpa [routeEq] using ends.2
  simp only [liftedStraightSegment,straightSegment,routeEq,List.head?_cons,List.getLast?_cons_cons,
    List.getLast?_singleton,Option.getD_some,firstEq,secondEq,GridSegment.translate]
  apply congrArg₂ GridSegment.mk <;> apply Prod.ext
  all_goals simp only [Cell.add,Cell.scale,periodTranslation,Prod.fst,Prod.snd] <;> ring

theorem straight_local_row_seam_bounds {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1) (cell : Cell) (row : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesHorizontalLine ((drawing.gridSize : Int)*row)) :
    tagged.1.offset.1 = 0 ∧
      (drawing.gridSize : ℚ)*cell.1 < (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row) ∧
      (drawing.liftedStraightSegment tagged.2 cell).rationalLineAbscissa ((drawing.gridSize : Int)*row) <
        (drawing.gridSize : ℚ)*(cell.1+1) := by
  have endpoints := compatible.1.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  have sourceBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem endpoints.1)
  have targetBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem endpoints.2)
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  rw [straight_lifted_segment_endpoints compatible member straight cell] at crosses ⊢
  exact GridSegment.local_horizontal_seam_abscissa_bounds positive sourceBounds targetBounds edgeLocal crosses

theorem seamCrossingAbscissae_interior {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {abscissa : ℚ} (member : abscissa ∈ seamCrossingAbscissae graph drawing 0) :
    0 < abscissa ∧ abscissa < (drawing.gridSize : ℚ) := by
  obtain ⟨key,keyMember,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have horizontalMember := (List.mem_filter.mp keyMember).1
  have data := List.mem_filter.mp horizontalMember
  obtain ⟨tagged,taggedMember,index,_⟩ := mem_nineEdgeCopies.mp data.1
  have crossed : (drawing.liftedStraightSegment tagged.2 key.2).CrossesHorizontalLine ((drawing.gridSize : Int)*0) := by
    simpa only [index,mul_zero] using (of_decide_eq_true data.2).1
  have bounds := straight_local_row_seam_bounds compatible taggedMember (straight tagged taggedMember)
    (graphLocal _ (List.fst_mem_of_mem_zipIdx taggedMember)) key.2 0 crossed
  simp only [index,mul_zero] at bounds
  have tableBounds := (of_decide_eq_true data.2).2
  have positive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have zeroCell : key.2.1 = 0 := by
    by_contra different
    rcases lt_or_gt_of_ne different with negative | positiveCell
    · have step : (key.2.1 : ℚ)+1 ≤ 0 := by exact_mod_cast (by omega : key.2.1+1 ≤ 0)
      nlinarith [bounds.2.2,tableBounds.1]
    · have step : (1 : ℚ) ≤ key.2.1 := by exact_mod_cast (by omega : 1 ≤ key.2.1)
      nlinarith [bounds.2.1,tableBounds.2]
  simpa only [zeroCell,Int.cast_zero,mul_zero,zero_add,mul_one] using bounds.2

end LeanTrominoes.PeriodicGridDrawing
