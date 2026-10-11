/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendFanGeometry
import LeanTrominoes.GridSegmentOrderedCoreDigitalRoutes

/-! # Bookkeeping port keys agree with the unshifted segment directions -/
namespace LeanTrominoes
namespace GridSegment

theorem rationalSlope_scale (segment : GridSegment) {factor : Int} (nonzero : factor ≠ 0) :
    (segment.scale factor).rationalSlope = segment.rationalSlope := by
  have rationalNonzero : (factor : ℚ) ≠ 0 := by exact_mod_cast nonzero
  simp only [rationalSlope,scale,Cell.scale,Int.cast_mul,← mul_sub]
  exact mul_div_mul_left _ _ rationalNonzero

theorem straightRayKey_scale (segment : GridSegment) {factor : Int} (positive : 0 < factor) :
    (segment.scale factor).straightRayKey = segment.straightRayKey := by
  unfold straightRayKey
  rw [rationalSlope_scale segment (ne_of_gt positive)]
  have order (first last : Int) : factor*first < factor*last ↔ first < last := by
    constructor
    · intro less
      by_contra wrong
      exact (not_le_of_gt less) (mul_le_mul_of_nonneg_left (le_of_not_gt wrong) positive.le)
    · intro less
      exact mul_lt_mul_of_pos_left less positive
  simp only [scale,Cell.scale,order]

end GridSegment
namespace PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing OrthogonalDrawingRefinement

theorem shifted_straightSegment {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    (shiftedDrawing source drawing).straightSegment tagged.2 =
      ((subdivisionSegment source drawing tagged.1).scale 2).translate (1,1) := by
  rw [straightSegment,shifted_edgeRoute_of_tagged source drawing member]
  simp only [shiftedRoute,List.head?_cons,List.getLast?_cons_cons,List.getLast?_singleton,Option.getD_some]
  unfold shiftedPosition subdivisionSegment GridSegment.translate GridSegment.scale
  congr 1
  all_goals apply Prod.ext <;> simp only [Cell.add,Cell.scale] <;> ring

theorem shifted_source_portRayKey {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    (shiftedDrawing source drawing).portRayKey (sourcePort tagged.1 tagged.2) =
      (subdivisionSegment source drawing tagged.1).straightRayKey := by
  change ((shiftedDrawing source drawing).straightSegment tagged.2).straightRayKey = _
  rw [shifted_straightSegment source drawing member,GridSegment.straightRayKey_translate,
    GridSegment.straightRayKey_scale _ (by decide)]

theorem shifted_target_portRayKey {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    (shiftedDrawing source drawing).portRayKey (targetPort tagged.1 tagged.2) =
      (subdivisionSegment source drawing tagged.1).reverse.straightRayKey := by
  change ((shiftedDrawing source drawing).straightSegment tagged.2).reverse.straightRayKey = _
  rw [shifted_straightSegment source drawing member]
  change (((subdivisionSegment source drawing tagged.1).reverse.scale 2).translate (1,1)).straightRayKey = _
  rw [GridSegment.straightRayKey_translate,GridSegment.straightRayKey_scale _ (by decide)]

theorem vertical_anchoredSegment_x {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (factor : Int) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (vertical : (subdivisionSegment source drawing tagged.1).start.1 = (subdivisionSegment source drawing tagged.1).finish.1) :
    (anchoredSegment source drawing factor tagged).start.1 = factor*(subdivisionSegment source drawing tagged.1).start.1 ∧
      (anchoredSegment source drawing factor tagged).finish.1 = factor*(subdivisionSegment source drawing tagged.1).finish.1 := by
  have first := fanAnchor_x planar degree (sourcePort_mem_allPorts _ member)
  have last := fanAnchor_x planar degree (targetPort_mem_allPorts _ member)
  rw [shifted_source_portRayKey source drawing member] at first
  rw [shifted_target_portRayKey source drawing member] at last
  simp only [GridSegment.straightRayKey,GridSegment.reverse,vertical,lt_self_iff_false,ite_false] at first last
  split_ifs at first last <;>
    simp only [BendFan.horizontalSign,mul_zero] at first last <;>
    simp [anchoredSegment,Cell.add,Cell.scale,first,last]

end PeriodicGridDrawing.RawBendSubdivision
end LeanTrominoes
