/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleCutPortClassification
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCrossingPieceWindow

/-! # Proper cuts have crossing ports; endpoint cuts have incidence ports -/
namespace LeanTrominoes.PeriodicGridDrawing
open GeneralVertexNormalization PeriodicOrthocrossing

theorem incidence_parent_prototype_line {Vertex : Type*}
    (drawing : PeriodicGridDrawing) (index : Nat) (cell : Cell)
    (tagged : PeriodicEdge Vertex × Nat) (target : Bool)
    (parent : (ColumnPortKey.incidence tagged target).parentKey = (index,Cell.scale (-1) cell)) :
    (drawing.outwardStraightSegment tagged target).start.1+(drawing.gridSize : Int)*cell.1 =
      if target then (drawing.liftedStraightSegment index (0,0)).finish.1
        else (drawing.liftedStraightSegment index (0,0)).start.1 := by
  have indices := congrArg Prod.fst parent
  have cells := congrArg Prod.snd parent
  change tagged.2 = index at indices
  change endpointCell tagged target = Cell.scale (-1) cell at cells
  unfold outwardStraightSegment
  rw [indices,cells]
  cases target <;> simp [liftedStraightSegment,GridSegment.translate,GridSegment.reverse,
    periodTranslation,Cell.add,Cell.scale]

theorem rectanglePort_crossing_of_proper_cut {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) (line : Int) (right : Bool)
    {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (parent : key.parentKey = (index,Cell.scale (-1) cell))
    (onCut : (rectanglePortOriginalPoint graph drawing column cell key).1 =
      (line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing))
    (crosses : (drawing.liftedStraightSegment index (0,0)).CrossesVerticalLine line) :
    key = .vertical right (.crossing (index,Cell.scale (-1) cell)) ∧
      line = (column : Int)+(if right then 1 else 0)+(drawing.gridSize : Int)*cell.1 := by
  obtain ⟨lineEq,raw,keyEq⟩ := rectanglePort_at_cut_boundary planar graphLocal straight column cell line right valid onCut
  subst key
  cases raw with
  | crossing raw => exact ⟨congrArg (fun raw => RectanglePortKey.vertical right (.crossing raw)) parent,lineEq⟩
  | incidence tagged target =>
    have endpoint := incidence_parent_prototype_line drawing index cell tagged target parent
    change tagged ∈ graph.edges.zipIdx ∧
      (drawing.outwardStraightSegment tagged target).start.1 = ((column+if right then 1 else 0 : Nat) : Int) ∧ _ at valid
    rw [valid.2.1] at endpoint
    have cutEq : line = if target then (drawing.liftedStraightSegment index (0,0)).finish.1
        else (drawing.liftedStraightSegment index (0,0)).start.1 := by
      cases right <;> simpa using lineEq.trans endpoint
    cases target <;> simp only [Bool.false_eq_true,if_false,if_true] at cutEq <;>
      rcases crosses with forward | backward <;> omega

theorem rectanglePort_incidence_of_endpoint_cut {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (column : Nat) (cell : Cell) (right target : Bool)
    {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (parent : key.parentKey = (tagged.2,Cell.scale (-1) cell))
    (onCut : (rectanglePortOriginalPoint graph drawing column cell key).1 =
      (if target then (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1
        else (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 : Int)+
        (if right then -columnPerturbation graph drawing else columnPerturbation graph drawing))
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    key = .vertical right (.incidence tagged target) ∧
      cell = if target then tagged.1.offset else (0,0) := by
  let line := if target then (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1
    else (drawing.liftedStraightSegment tagged.2 (0,0)).start.1
  obtain ⟨lineEq,raw,keyEq⟩ := rectanglePort_at_cut_boundary planar graphLocal straight column cell line right valid onCut
  subst key
  have castAdd : ((column+if right then 1 else 0 : Nat) : Int) = (column : Int)+(if right then 1 else 0) := by
    split_ifs <;> simp
  cases raw with
  | crossing raw =>
    change raw = (tagged.2,Cell.scale (-1) cell) at parent
    subst raw
    have crosses := (of_decide_eq_true (List.mem_filter.mp valid).2).1
    have segmentEq : drawing.liftedStraightSegment tagged.2 (Cell.scale (-1) cell) =
        (drawing.liftedStraightSegment tagged.2 (0,0)).translate (drawing.periodTranslation (Cell.scale (-1) cell)) := by
      simpa only [Cell.add,zero_add] using liftedStraightSegment_add_cell drawing tagged.2 (0,0) (Cell.scale (-1) cell)
    have translatedLine : ((column+if right then 1 else 0 : Nat) : Int) =
        line+(drawing.periodTranslation (Cell.scale (-1) cell)).1 := by
      rw [castAdd,lineEq]
      simp [periodTranslation,Cell.scale]
    rw [segmentEq,translatedLine] at crosses
    have globalCrosses := (GridSegment.crossesVerticalLine_translate _ _ _).mp crosses
    cases target <;> simp only [line,Bool.false_eq_true,if_false,if_true] at globalCrosses <;>
      rcases globalCrosses with forward | backward <;> omega
  | incidence other otherTarget =>
    have indices := congrArg Prod.fst parent
    change other.2 = tagged.2 at indices
    have otherEq := tagged_eq_of_mem_zipIdx_of_snd_eq valid.1 member indices
    subst other
    have endpoint := incidence_parent_prototype_line drawing tagged.2 cell tagged otherTarget parent
    rw [valid.2.1,castAdd,← lineEq] at endpoint
    have targets : otherTarget = target := by
      cases target <;> cases otherTarget <;> simp only [line,Bool.false_eq_true,if_false,if_true] at endpoint <;>
        first | rfl | exact (nonvertical endpoint.symm).elim | exact (nonvertical endpoint).elim
    subst otherTarget
    refine ⟨rfl,?_⟩
    have cells := congrArg Prod.snd parent
    change endpointCell tagged target = Cell.scale (-1) cell at cells
    cases target <;> apply Prod.ext <;> simp [endpointCell,Cell.scale,Prod.ext_iff] at cells ⊢ <;> omega

end LeanTrominoes.PeriodicGridDrawing
