/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectanglePortParents
import LeanTrominoes.PeriodicGridDrawingPeriodicSeamCrossingTable

/-! # The rectangle matching's nine-copy window includes every port parent -/
namespace LeanTrominoes.PeriodicGridDrawing
open GeneralVertexNormalization PeriodicOrthocrossing

theorem endpointCell_mem_neighborTranslations {Vertex : Type*} {tagged : PeriodicEdge Vertex × Nat}
    (edgeLocal : tagged.1.span ≤ 1) (target : Bool) : endpointCell tagged target ∈ neighborTranslations := by
  unfold PeriodicEdge.span at edgeLocal
  apply (mem_neighborTranslations_iff _).mpr
  cases target
  · simp [endpointCell,IsNeighborTranslation]
  · have bounds : -1 ≤ tagged.1.offset.1 ∧ tagged.1.offset.1 ≤ 1 ∧
        -1 ≤ tagged.1.offset.2 ∧ tagged.1.offset.2 ≤ 1 := by omega
    simp only [endpointCell,if_true,Cell.scale,IsNeighborTranslation]
    constructor <;> omega

theorem rectanglePort_parent_mem_nineEdgeCopies {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    key.parentKey ∈ nineEdgeCopies graph := by
  cases key with
  | vertical right key =>
    cases key with
    | crossing key => exact (List.mem_filter.mp valid).1
    | incidence tagged target =>
      exact mem_nineEdgeCopies.mpr ⟨tagged,valid.1,rfl,
        endpointCell_mem_neighborTranslations (graphLocal _ (List.fst_mem_of_mem_zipIdx valid.1)) target⟩
  | horizontal top key =>
    have horizontalMember := (List.mem_filter.mp valid.1).1
    have data := List.mem_filter.mp horizontalMember
    obtain ⟨tagged,member,index,_⟩ := mem_nineEdgeCopies.mp data.1
    have crosses := (of_decide_eq_true data.2).1
    have bounds := (of_decide_eq_true data.2).2
    rw [← index] at crosses bounds
    let shift : Cell := (0,if top then 1 else 0)
    have translatedCrosses : (drawing.liftedStraightSegment tagged.2 (Cell.add key.2 shift)).CrossesHorizontalLine
        ((drawing.gridSize : Int)*(if top then 1 else 0)) := by
      rw [liftedStraightSegment_add_cell]
      have lineEqual : (drawing.gridSize : Int)*(if top then 1 else 0) = 0+(drawing.periodTranslation shift).2 := by
        cases top <;> simp [shift,periodTranslation,Cell.scale]
      rw [lineEqual,GridSegment.crossesHorizontalLine_translate]
      exact crosses
    have translatedBounds : 0 ≤ (drawing.liftedStraightSegment tagged.2 (Cell.add key.2 shift)).rationalLineAbscissa
          ((drawing.gridSize : Int)*(if top then 1 else 0)) ∧
        (drawing.liftedStraightSegment tagged.2 (Cell.add key.2 shift)).rationalLineAbscissa
          ((drawing.gridSize : Int)*(if top then 1 else 0)) < (drawing.gridSize : ℚ) := by
      rw [liftedStraightSegment_add_cell]
      have lineEqual : (drawing.gridSize : Int)*(if top then 1 else 0) = 0+(drawing.periodTranslation shift).2 := by
        cases top <;> simp [shift,periodTranslation,Cell.scale]
      rw [lineEqual,GridSegment.rationalLineAbscissa_translate]
      simpa [shift,periodTranslation,Cell.scale] using bounds
    have lineBounds : 0 ≤ (drawing.gridSize : Int)*(if top then 1 else 0) ∧
        (drawing.gridSize : Int)*(if top then 1 else 0) ≤ drawing.gridSize := by cases top <;> simp
    have copy := horizontalCrossingCopies_complete compatible member (straight tagged member)
      (graphLocal _ (List.fst_mem_of_mem_zipIdx member)) lineBounds (Cell.add key.2 shift) translatedCrosses translatedBounds
    simpa only [RectanglePortKey.parentKey,index,shift] using (List.mem_filter.mp copy).1

end LeanTrominoes.PeriodicGridDrawing
