/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RealRectangleBoundaryChordCardinality

/-! # A segment not supported by a rectangle face has one port on that face -/
namespace LeanTrominoes.GridSegment

theorem realContains_eq_of_same_x {segment : GridSegment} {first second : ℝ × ℝ}
    (firstContains : segment.RealContains first) (secondContains : segment.RealContains second)
    (sameX : first.1 = second.1) (away : (segment.start.1 : ℝ) ≠ first.1) : first = second := by
  obtain ⟨u,_,_,ux,uy⟩ := firstContains
  obtain ⟨v,_,_,vx,vy⟩ := secondContains
  have product : (u-v)*((segment.finish.1 : ℝ)-segment.start.1) = 0 := by nlinarith
  rcases mul_eq_zero.mp product with sameParameter | constant
  · have parameters := sub_eq_zero.mp sameParameter
    apply Prod.ext sameX
    rw [parameters] at uy
    linarith
  · rw [constant,mul_zero,add_zero] at ux
    exact (away ux.symm).elim

theorem realContains_eq_of_same_y {segment : GridSegment} {first second : ℝ × ℝ}
    (firstContains : segment.RealContains first) (secondContains : segment.RealContains second)
    (sameY : first.2 = second.2) (away : (segment.start.2 : ℝ) ≠ first.2) : first = second := by
  obtain ⟨u,_,_,ux,uy⟩ := firstContains
  obtain ⟨v,_,_,vx,vy⟩ := secondContains
  have product : (u-v)*((segment.finish.2 : ℝ)-segment.start.2) = 0 := by nlinarith
  rcases mul_eq_zero.mp product with sameParameter | constant
  · have parameters := sub_eq_zero.mp sameParameter
    apply Prod.ext _ sameY
    rw [parameters] at ux
    linarith
  · rw [constant,mul_zero,add_zero] at uy
    exact (away uy.symm).elim

end LeanTrominoes.GridSegment
namespace LeanTrominoes.RealRectangleBoundary

theorem ports_eq_of_same_side {origin : ℝ × ℝ} {width height : ℝ} {first last : Port} {segment : GridSegment}
    (leftAway : (segment.start.1 : ℝ) ≠ origin.1) (rightAway : (segment.start.1 : ℝ) ≠ origin.1+width)
    (bottomAway : (segment.start.2 : ℝ) ≠ origin.2) (topAway : (segment.start.2 : ℝ) ≠ origin.2+height)
    (sameSide : first.side = last.side)
    (firstContains : segment.RealContains (first.shiftedPoint origin width height))
    (lastContains : segment.RealContains (last.shiftedPoint origin width height)) : first = last := by
  obtain ⟨side,firstCoordinate⟩ := first
  obtain ⟨lastSide,lastCoordinate⟩ := last
  dsimp only at sameSide
  subst lastSide
  have coordinates : firstCoordinate = lastCoordinate := by
    fin_cases side
    · have samePoint := GridSegment.realContains_eq_of_same_x firstContains lastContains rfl (by simpa [Port.shiftedPoint,Port.point] using leftAway)
      have equal := congrArg Prod.snd samePoint
      simp [Port.shiftedPoint,Port.point] at equal
      linarith
    · have samePoint := GridSegment.realContains_eq_of_same_y firstContains lastContains rfl (by simpa [Port.shiftedPoint,Port.point] using topAway)
      have equal := congrArg Prod.fst samePoint
      simp [Port.shiftedPoint,Port.point] at equal
      linarith
    · have samePoint := GridSegment.realContains_eq_of_same_x firstContains lastContains rfl (by simpa [Port.shiftedPoint,Port.point] using rightAway)
      have equal := congrArg Prod.snd samePoint
      simp [Port.shiftedPoint,Port.point] at equal
      linarith
    · have samePoint := GridSegment.realContains_eq_of_same_y firstContains lastContains rfl (by simpa [Port.shiftedPoint,Port.point] using bottomAway)
      have equal := congrArg Prod.fst samePoint
      simp [Port.shiftedPoint,Port.point] at equal
      linarith
  subst lastCoordinate
  rfl

end LeanTrominoes.RealRectangleBoundary
