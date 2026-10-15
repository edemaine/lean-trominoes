/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingIncidenceCutTranslation
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingColumnCutClassification
import LeanTrominoes.Common.Geometry.GridSegmentRationalHeightReverse

/-! # Endpoint column cuts are retained as prototype incidence ports -/
namespace LeanTrominoes.PeriodicGridDrawing
open GeneralVertexNormalization

theorem outwardStraightSegment_translate {Vertex : Type*} (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) (target : Bool) (cell : Cell) :
    (drawing.outwardStraightSegment tagged target).translate (drawing.periodTranslation cell) =
      if target then (drawing.liftedStraightSegment tagged.2 (Cell.add (endpointCell tagged target) cell)).reverse else
        drawing.liftedStraightSegment tagged.2 (Cell.add (endpointCell tagged target) cell) := by
  rw [liftedStraightSegment_add_cell]
  cases target <;> rfl

theorem endpoint_cut_retained_of_virtual_row {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target right : Bool)
    (shift : Cell) {line : Int} (lineBounds : 0 ≤ line ∧ line ≤ drawing.gridSize)
    (sameX : (drawing.outwardStraightSegment tagged target).start.1+(drawing.gridSize : Int)*shift.1 = line)
    (direction : if right then (drawing.outwardStraightSegment tagged target).finish.1 <
        (drawing.outwardStraightSegment tagged target).start.1 else
      (drawing.outwardStraightSegment tagged target).start.1 < (drawing.outwardStraightSegment tagged target).finish.1)
    (inside : -seamPerturbation graph drawing <
        ((drawing.outwardStraightSegment tagged target).translate (drawing.periodTranslation shift)).rationalHeightAt
          ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)) ∧
      ((drawing.outwardStraightSegment tagged target).translate (drawing.periodTranslation shift)).rationalHeightAt
          ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)) <
        (drawing.gridSize : ℚ)-seamPerturbation graph drawing) :
    shift = (0,0) ∧ (ColumnPortKey.incidence tagged target).Valid graph drawing line right := by
  have coordinateEqual : (line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) =
      ((drawing.outwardStraightSegment tagged target).start.1 : ℚ)+
        (if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)+(drawing.periodTranslation shift).1 := by
    have castX : ((drawing.outwardStraightSegment tagged target).start.1 : ℚ)+(drawing.gridSize : ℚ)*shift.1 = line := by exact_mod_cast sameX
    simp only [periodTranslation,Cell.scale,Int.cast_mul,Int.cast_natCast]
    linarith
  rw [coordinateEqual,translated_outward_cut_height] at inside
  have zero := translated_incidence_cell_zero planar straight member target right shift lineBounds sameX inside
  refine ⟨zero,member,?_,?_⟩
  · simpa only [zero,Prod.fst,mul_zero,add_zero] using sameX
  · rw [← outwardStraightSegment_key]
    cases right
    · have forward : (drawing.outwardStraightSegment tagged target).start.1 <
          (drawing.outwardStraightSegment tagged target).finish.1 := direction
      simp [GridSegment.straightRayKey,forward]
    · have backward : (drawing.outwardStraightSegment tagged target).finish.1 <
          (drawing.outwardStraightSegment tagged target).start.1 := direction
      have notForward : ¬ (drawing.outwardStraightSegment tagged target).start.1 <
          (drawing.outwardStraightSegment tagged target).finish.1 := by omega
      simp [GridSegment.straightRayKey,notForward,backward]

end LeanTrominoes.PeriodicGridDrawing
