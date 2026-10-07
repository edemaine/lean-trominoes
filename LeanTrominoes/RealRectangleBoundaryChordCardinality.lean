/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RealRectangleBoundaryShiftedNoninterlacing

/-! # A straight segment has at most two proper rectangle boundary ports -/
namespace LeanTrominoes.GridSegment

theorem orientedArea_eq_zero_of_realContains {segment : GridSegment} {a b c : ℝ × ℝ}
    (aContains : segment.RealContains a) (bContains : segment.RealContains b) (cContains : segment.RealContains c) :
    orientedArea a b c = 0 := by
  obtain ⟨_,_,_,ax,ay⟩ := aContains
  obtain ⟨_,_,_,bx,bY⟩ := bContains
  obtain ⟨_,_,_,cx,cy⟩ := cContains
  simp only [orientedArea,ax,ay,bx,bY,cx,cy]
  ring

end LeanTrominoes.GridSegment
namespace LeanTrominoes.RealRectangleBoundary

theorem three_ordered_ports_same_side {origin : ℝ × ℝ} {width height : ℝ} {first middle last : Port} {segment : GridSegment}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (firstInside : first.Inside width height) (middleInside : middle.Inside width height) (lastInside : last.Inside width height)
    (firstOrder : first.Before middle) (lastOrder : middle.Before last)
    (firstContains : segment.RealContains (first.shiftedPoint origin width height))
    (middleContains : segment.RealContains (middle.shiftedPoint origin width height))
    (lastContains : segment.RealContains (last.shiftedPoint origin width height)) : first.side = last.side := by
  by_contra different
  have positive := orientedArea_positive_between widthPositive heightPositive firstInside middleInside lastInside firstOrder lastOrder different
  have zero := GridSegment.orientedArea_eq_zero_of_realContains firstContains lastContains middleContains
  rw [orientedArea_shiftedPoint] at zero
  linarith

theorem ordered_boundary_ports_length_le_two {origin : ℝ × ℝ} {width height : ℝ} {segment : GridSegment} {ports : List Port}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (ordered : ports.Pairwise Port.Before)
    (inside : ∀ port ∈ ports, port.Inside width height)
    (contains : ∀ port ∈ ports, segment.RealContains (port.shiftedPoint origin width height))
    (uniqueSide : ∀ first ∈ ports, ∀ last ∈ ports, first.side = last.side → first = last) : ports.length ≤ 2 := by
  cases ports with
  | nil => simp
  | cons first rest =>
    cases rest with
    | nil => simp
    | cons middle rest =>
      cases rest with
      | nil => simp
      | cons last rest =>
        have firstMember : first ∈ first :: middle :: last :: rest := by simp
        have middleMember : middle ∈ first :: middle :: last :: rest := by simp
        have lastMember : last ∈ first :: middle :: last :: rest := by simp
        have firstOrder := (List.pairwise_cons.mp ordered).1 middle (by simp)
        have lastOrder := (List.pairwise_cons.mp (List.pairwise_cons.mp ordered).2).1 last (by simp)
        have same := three_ordered_ports_same_side widthPositive heightPositive
          (inside first firstMember) (inside middle middleMember) (inside last lastMember) firstOrder lastOrder
          (contains first firstMember) (contains middle middleMember) (contains last lastMember)
        have equal := uniqueSide first firstMember last lastMember same
        have wholeOrder : first.Before last := lt_trans firstOrder lastOrder
        rw [equal] at wholeOrder
        exact (lt_irrefl _ wholeOrder).elim

end LeanTrominoes.RealRectangleBoundary
