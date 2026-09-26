/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingArithmeticGeometry
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificate

/-! # Native arithmetic checks of orthogonality and the open one-cell halo -/
namespace LeanTrominoes.PeriodicGridDrawing.HaloGuard
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry Arithmetic

def axisAligned (s : Segment) : Expr := orE (horizontal s) (vertical s)
def inHalo (period : Expr) (p : Point) : Expr :=
  andE (less (difference 0 period) p.1) (andE (less p.1 (difference (2*period) 0))
    (andE (less (difference 0 period) p.2) (less p.2 (difference (2*period) 0))))
def segmentHalo (period : Expr) (s : Segment) : Expr := andE (inHalo period s.start) (inHalo period s.finish)
def orthogonal : Expr := .all (var 2) (axisAligned (segment 1 (var 0)))
def halo : Expr := .all (var 2) (segmentHalo (var 1) (segment 1 (var 0)))

theorem axisAligned_truth (s : Segment) (values : List Nat) :
    (axisAligned s).Truth values ↔ (s.eval values).IsAxisAligned := by
  rw [axisAligned,truth_or,horizontal_truth,vertical_truth]
  rfl

theorem inHalo_truth (period : Expr) (p : Point) (values : List Nat) :
    (inHalo period p).Truth values ↔
      -(period.eval values:Int) < (pointEval p values).1 ∧
      (pointEval p values).1 < 2*(period.eval values:Int) ∧
      -(period.eval values:Int) < (pointEval p values).2 ∧
      (pointEval p values).2 < 2*(period.eval values:Int) := by
  simp [inHalo,truth_and,less_truth,difference_eval,pointEval,Expr.eval,Op.eval]

theorem segmentHalo_truth (period : Expr) (s : Segment) (values : List Nat) (d : PeriodicGridDrawing)
    (he : period.eval values = d.gridSize) :
    (segmentHalo period s).Truth values ↔
      d.PositionInExpandedSquare (s.eval values).start ∧ d.PositionInExpandedSquare (s.eval values).finish := by
  rw [segmentHalo,truth_and,inHalo_truth,inHalo_truth,he]
  rfl

theorem orthogonal_truth (d : PeriodicGridDrawing) : orthogonal.Truth (fields d) ↔ d.IsOrthogonal := by
  rw [orthogonal,truth_all]
  change (∀ i < d.indexedSegments.length, (axisAligned (segment 1 (var 0))).Truth (i::fields d)) ↔ _
  have body (i : Nat) (hi : i < d.indexedSegments.length) :
      (axisAligned (segment 1 (var 0))).Truth (i::fields d) ↔ d.indexedSegments[i].segment.IsAxisAligned := by
    rw [axisAligned_truth]
    have h := segment_eval d [i] (var 0) i rfl hi
    exact congrArg GridSegment.IsAxisAligned h |>.to_iff
  constructor
  · intro h s hs
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hs
    exact (body i hi).mp (h i hi)
  · intro h i hi
    exact (body i hi).mpr (h _ (List.getElem_mem hi))

theorem halo_truth (d : PeriodicGridDrawing) : halo.Truth (fields d) ↔ d.SegmentEndpointsInExpandedSquare := by
  rw [halo,truth_all]
  change (∀ i < d.indexedSegments.length, (segmentHalo (var 1) (segment 1 (var 0))).Truth (i::fields d)) ↔ _
  have body (i : Nat) (hi : i < d.indexedSegments.length) :
      (segmentHalo (var 1) (segment 1 (var 0))).Truth (i::fields d) ↔
        d.PositionInExpandedSquare d.indexedSegments[i].segment.start ∧
        d.PositionInExpandedSquare d.indexedSegments[i].segment.finish := by
    rw [segmentHalo_truth _ _ _ d rfl]
    have h := segment_eval d [i] (var 0) i rfl hi
    change (segment 1 (var 0)).eval (i::fields d) = d.indexedSegments[i].segment at h
    rw [h]
  constructor
  · intro h s hs
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hs
    exact (body i hi).mp (h i hi)
  · intro h i hi
    exact (body i hi).mpr (h _ (List.getElem_mem hi))

theorem orthogonal_noPower : orthogonal.noPower = true := by decide
theorem halo_noPower : halo.noPower = true := by decide

end LeanTrominoes.PeriodicGridDrawing.HaloGuard
