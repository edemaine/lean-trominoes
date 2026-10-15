/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealTube
import LeanTrominoes.Common.Geometry.GridSegmentRealIntersection
import Mathlib.Algebra.Order.Floor.Ring

/-! # Integer samples of an arbitrary straight segment

Uniform samples with coordinate increments at most one are rounded down to
the integer grid. Sample points have coordinate error at most one; the
horizontal-then-vertical corners between consecutive samples have error at
most two. The endpoints remain exact.
-/
namespace LeanTrominoes.GridSegment

def digitalSteps (segment : GridSegment) : Nat :=
  segment.direction.1.natAbs+segment.direction.2.natAbs+1

theorem digitalSteps_positive (segment : GridSegment) : 0 < segment.digitalSteps := by
  unfold digitalSteps
  omega

theorem digitalSteps_direction_bounds (segment : GridSegment) :
    |(segment.direction.1 : ℝ)| ≤ segment.digitalSteps ∧
      |(segment.direction.2 : ℝ)| ≤ segment.digitalSteps := by
  simp only [digitalSteps,Nat.cast_add,Nat.cast_one,Nat.cast_natAbs,Int.cast_abs]
  constructor <;> linarith [abs_nonneg (segment.direction.1 : ℝ),abs_nonneg (segment.direction.2 : ℝ)]

noncomputable def digitalSampleReal (segment : GridSegment) (index : Nat) : ℝ × ℝ :=
  ((segment.start.1 : ℝ)+(index : ℝ)/segment.digitalSteps*(segment.direction.1 : ℝ),
    (segment.start.2 : ℝ)+(index : ℝ)/segment.digitalSteps*(segment.direction.2 : ℝ))

noncomputable def digitalSample (segment : GridSegment) (index : Nat) : Cell :=
  (⌊(segment.digitalSampleReal index).1⌋,⌊(segment.digitalSampleReal index).2⌋)

theorem digitalSampleReal_contains (segment : GridSegment) {index : Nat}
    (valid : index ≤ segment.digitalSteps) : segment.RealContains (segment.digitalSampleReal index) := by
  have positive : (0 : ℝ) < segment.digitalSteps := by exact_mod_cast segment.digitalSteps_positive
  refine ⟨(index : ℝ)/segment.digitalSteps,by positivity,?_,?_,?_⟩
  · exact (div_le_one positive).mpr (by exact_mod_cast valid)
  · simp [digitalSampleReal,direction]
  · simp [digitalSampleReal,direction]

theorem floor_error (value : ℝ) : |(⌊value⌋ : ℝ)-value| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [Int.floor_le value,Int.lt_floor_add_one value]

theorem digitalSample_error (segment : GridSegment) (index : Nat) :
    |(segment.digitalSample index).1-(segment.digitalSampleReal index).1| ≤ (1 : ℝ) ∧
      |(segment.digitalSample index).2-(segment.digitalSampleReal index).2| ≤ (1 : ℝ) :=
  ⟨floor_error _,floor_error _⟩

theorem digitalSample_tube (segment : GridSegment) {index : Nat} (valid : index ≤ segment.digitalSteps) :
    segment.RealTubeContains 1 ((segment.digitalSample index).1,(segment.digitalSample index).2) :=
  ⟨segment.digitalSampleReal index,segment.digitalSampleReal_contains valid,segment.digitalSample_error index⟩

theorem digitalSampleReal_increment (segment : GridSegment) (index : Nat) :
    |(segment.digitalSampleReal (index+1)).1-(segment.digitalSampleReal index).1| ≤ 1 ∧
      |(segment.digitalSampleReal (index+1)).2-(segment.digitalSampleReal index).2| ≤ 1 := by
  have positive : (0 : ℝ) < segment.digitalSteps := by exact_mod_cast segment.digitalSteps_positive
  have bounds := segment.digitalSteps_direction_bounds
  have coordinate (start delta : ℝ) (bound : |delta| ≤ segment.digitalSteps) :
      |(start+((index+1 : Nat) : ℝ)/segment.digitalSteps*delta)-
        (start+(index : ℝ)/segment.digitalSteps*delta)| ≤ 1 := by
    have equal : (start+((index+1 : Nat) : ℝ)/segment.digitalSteps*delta)-
        (start+(index : ℝ)/segment.digitalSteps*delta) = delta/segment.digitalSteps := by
      push_cast
      ring
    rw [equal,abs_div,abs_of_pos positive]
    exact (div_le_one positive).mpr bound
  exact ⟨coordinate _ _ bounds.1,coordinate _ _ bounds.2⟩

theorem digitalSample_corner_tube (segment : GridSegment) {index : Nat}
    (valid : index < segment.digitalSteps) :
    segment.RealTubeContains 2 ((segment.digitalSample (index+1)).1,(segment.digitalSample index).2) := by
  have firstError := segment.digitalSample_error index
  have nextError := segment.digitalSample_error (index+1)
  have increment := segment.digitalSampleReal_increment index
  refine ⟨segment.digitalSampleReal index,segment.digitalSampleReal_contains (by omega),?_,?_⟩
  · calc
      _ = |((segment.digitalSample (index+1)).1-(segment.digitalSampleReal (index+1)).1)+
          ((segment.digitalSampleReal (index+1)).1-(segment.digitalSampleReal index).1)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ 2 := by linarith [nextError.1,increment.1]
  · exact firstError.2.trans (by norm_num)

@[simp] theorem digitalSample_zero (segment : GridSegment) : segment.digitalSample 0 = segment.start := by
  simp [digitalSample,digitalSampleReal]

@[simp] theorem digitalSample_last (segment : GridSegment) :
    segment.digitalSample segment.digitalSteps = segment.finish := by
  have nonzero : (segment.digitalSteps : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt segment.digitalSteps_positive
  have x : (segment.digitalSampleReal segment.digitalSteps).1 = segment.finish.1 := by
    simp [digitalSampleReal,direction,nonzero]
  have y : (segment.digitalSampleReal segment.digitalSteps).2 = segment.finish.2 := by
    simp [digitalSampleReal,direction,nonzero]
  simp [digitalSample,x,y]

theorem digitalSample_box (segment : GridSegment) {index : Nat} (valid : index ≤ segment.digitalSteps) :
    min segment.start.1 segment.finish.1 ≤ (segment.digitalSample index).1 ∧
      (segment.digitalSample index).1 ≤ max segment.start.1 segment.finish.1 ∧
      min segment.start.2 segment.finish.2 ≤ (segment.digitalSample index).2 ∧
      (segment.digitalSample index).2 ≤ max segment.start.2 segment.finish.2 := by
  have box := realBoxContains_of_realContains (segment.digitalSampleReal_contains valid)
  have coordinate (lower upper : Int) (value : ℝ) (lo : (lower : ℝ) ≤ value) (hi : value ≤ upper) :
      lower ≤ ⌊value⌋ ∧ ⌊value⌋ ≤ upper := by
    refine ⟨Int.le_floor.mpr lo,Int.floor_le_iff.mpr ?_⟩
    linarith
  exact ⟨(coordinate _ _ _ box.1 box.2.1).1,(coordinate _ _ _ box.1 box.2.1).2,
    (coordinate _ _ _ box.2.2.1 box.2.2.2).1,(coordinate _ _ _ box.2.2.1 box.2.2.2).2⟩

noncomputable def digitalSamples (segment : GridSegment) (first : Nat) : Nat → List Cell
  | 0 => [segment.digitalSample first]
  | length+1 => segment.digitalSample first :: segment.digitalSamples (first+1) length

@[simp] theorem digitalSamples_head (segment : GridSegment) (first length : Nat) :
    (segment.digitalSamples first length).head? = some (segment.digitalSample first) := by
  cases length <;> rfl

@[simp] theorem digitalSamples_last (segment : GridSegment) (first length : Nat) :
    (segment.digitalSamples first length).getLast? = some (segment.digitalSample (first+length)) := by
  induction length generalizing first with
  | zero => simp [digitalSamples]
  | succ length induction =>
      cases length with
      | zero => simp [digitalSamples]
      | succ length =>
          rw [digitalSamples,digitalSamples,List.getLast?_cons_cons]
          change (segment.digitalSamples (first+1) (length+1)).getLast? =
            some (segment.digitalSample (first+(length+1+1)))
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using induction (first+1)

theorem digitalSamples_member {segment : GridSegment} {first length : Nat} {point : Cell}
    (member : point ∈ segment.digitalSamples first length) :
    ∃ index, first ≤ index ∧ index ≤ first+length ∧ point = segment.digitalSample index := by
  induction length generalizing first with
  | zero =>
      simp only [digitalSamples,List.mem_singleton] at member
      exact ⟨first,le_rfl,by omega,member⟩
  | succ length induction =>
      simp only [digitalSamples,List.mem_cons] at member
      rcases member with equal | member
      · exact ⟨first,le_rfl,by omega,equal⟩
      · obtain ⟨index,lower,upper,equal⟩ := induction member
        exact ⟨index,by omega,by omega,equal⟩

theorem digitalSamples_segment {segment piece : GridSegment} {first length : Nat}
    (member : piece ∈ gridPolylineSegments (segment.digitalSamples first length)) :
    ∃ index, first ≤ index ∧ index < first+length ∧
      piece = ⟨segment.digitalSample index,segment.digitalSample (index+1)⟩ := by
  induction length generalizing first with
  | zero => simp [digitalSamples,gridPolylineSegments] at member
  | succ length induction =>
      have decomposition : gridPolylineSegments (segment.digitalSamples first (length+1)) =
          ⟨segment.digitalSample first,segment.digitalSample (first+1)⟩ ::
            gridPolylineSegments (segment.digitalSamples (first+1) length) := by
        cases length <;> rfl
      rw [decomposition,List.mem_cons] at member
      rcases member with equal | member
      · exact ⟨first,le_rfl,by omega,equal⟩
      · obtain ⟨index,lower,upper,equal⟩ := induction member
        exact ⟨index,by omega,by omega,equal⟩

end LeanTrominoes.GridSegment
