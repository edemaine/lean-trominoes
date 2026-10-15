/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentKickedDigitalRoute

/-! # Endpoint boxes and port-column contacts of kicked digital routes

The rasterized middle is strictly inside the port columns. Consequently
the complete route meets either exterior half-plane only at its own port.
This also applies to leftward cores and preserves the endpoint rectangle.
-/
namespace LeanTrominoes.GridSegment

theorem kickedSegment_horizontal_bounds {segment : GridSegment} {side : Int}
    (unit : side = 1 ∨ side = -1) (wide : 3 ≤ side*(segment.finish.1-segment.start.1))
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (segment.kickedSegment side).digitalRoute point) :
    0 < (side : ℝ)*(point.1-segment.start.1) ∧
      0 < (side : ℝ)*((segment.finish.1 : ℝ)-point.1) := by
  have bounds := (segment.kickedSegment side).digitalRoute_box contains
  rcases unit with rfl | rfl
  · have increasing : segment.start.1+1 ≤ segment.finish.1-1 := by omega
    simp only [RealBoxContains,kickedSegment,min_eq_left increasing,max_eq_right increasing,
      Int.cast_add,Int.cast_sub,Int.cast_one,one_mul] at bounds ⊢
    constructor <;> linarith [bounds.1,bounds.2.1]
  · have decreasing : segment.finish.1+1 ≤ segment.start.1-1 := by omega
    have first : segment.start.1+(-1) = segment.start.1-1 := by omega
    have last : segment.finish.1-(-1) = segment.finish.1+1 := by omega
    simp only [RealBoxContains,kickedSegment,first,last,
      min_eq_right decreasing,max_eq_left decreasing,Int.cast_add,Int.cast_sub,Int.cast_one] at bounds
    norm_num
    constructor <;> linarith [bounds.1,bounds.2.1]

theorem startKick_bounds {segment : GridSegment} {side : Int} (unit : side = 1 ∨ side = -1)
    {point : ℝ × ℝ}
    (contains : (⟨segment.start,(segment.kickedSegment side).start⟩ : GridSegment).RealContains point) :
    0 ≤ (side : ℝ)*(point.1-segment.start.1) ∧
      (side : ℝ)*(point.1-segment.start.1) ≤ 1 ∧ point.2 = (segment.start.2 : ℝ) := by
  obtain ⟨t,lower,upper,x,y⟩ := contains
  rcases unit with rfl | rfl <;>
    simp [kickedSegment] at x y ⊢ <;>
    exact ⟨by linarith,by linarith,y⟩

theorem finishKick_bounds {segment : GridSegment} {side : Int} (unit : side = 1 ∨ side = -1)
    {point : ℝ × ℝ}
    (contains : (⟨(segment.kickedSegment side).finish,segment.finish⟩ : GridSegment).RealContains point) :
    0 ≤ (side : ℝ)*((segment.finish.1 : ℝ)-point.1) ∧
      (side : ℝ)*((segment.finish.1 : ℝ)-point.1) ≤ 1 ∧ point.2 = (segment.finish.2 : ℝ) := by
  obtain ⟨t,lower,upper,x,y⟩ := contains
  rcases unit with rfl | rfl <;>
    simp [kickedSegment] at x y ⊢ <;>
    exact ⟨by linarith,by linarith,y⟩

theorem kickedDigitalWalk_exterior_contacts {segment : GridSegment} {side : Int}
    (unit : side = 1 ∨ side = -1) (wide : 3 ≤ side*(segment.finish.1-segment.start.1))
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (segment.kickedDigitalWalk side) point) :
    ((side : ℝ)*(point.1-segment.start.1) ≤ 0 → point = realCell segment.start) ∧
      ((side : ℝ)*((segment.finish.1 : ℝ)-point.1) ≤ 0 → point = realCell segment.finish) := by
  have realWide : (3 : ℝ) ≤ (side : ℝ)*((segment.finish.1 : ℝ)-segment.start.1) := by
    exact_mod_cast wide
  rcases (segment.kickedDigitalWalk_contains side point).mp contains with first | middle | last
  · have bounds := startKick_bounds unit first
    constructor
    · intro outside
      have zero : (side : ℝ)*(point.1-segment.start.1) = 0 := by linarith
      apply Prod.ext
      · rcases unit with rfl | rfl <;> dsimp [realCell] <;> norm_num at zero <;> linarith
      · exact bounds.2.2
    · intro outside
      nlinarith [bounds.2.1]
  · have bounds := kickedSegment_horizontal_bounds unit wide middle
    constructor <;> intro outside <;> linarith
  · have bounds := finishKick_bounds unit last
    constructor
    · intro outside
      nlinarith [bounds.2.1]
    · intro outside
      have zero : (side : ℝ)*((segment.finish.1 : ℝ)-point.1) = 0 := by linarith
      apply Prod.ext
      · rcases unit with rfl | rfl <;> dsimp [realCell] <;> norm_num at zero <;> linarith
      · exact bounds.2.2

theorem kickedDigitalRoute_exterior_contacts {segment : GridSegment} {side : Int}
    (unit : side = 1 ∨ side = -1) (wide : 3 ≤ side*(segment.finish.1-segment.start.1))
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (segment.kickedDigitalRoute side) point) :
    ((side : ℝ)*(point.1-segment.start.1) ≤ 0 → point = realCell segment.start) ∧
      ((side : ℝ)*((segment.finish.1 : ℝ)-point.1) ≤ 0 → point = realCell segment.finish) :=
  kickedDigitalWalk_exterior_contacts unit wide
    (kickedDigitalRoute_contains (by rcases unit with rfl | rfl <;> norm_num) contains)

theorem kickedDigitalWalk_box {segment : GridSegment} {side : Int}
    (unit : side = 1 ∨ side = -1) (wide : 3 ≤ side*(segment.finish.1-segment.start.1))
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (segment.kickedDigitalWalk side) point) :
    segment.RealBoxContains point := by
  rcases (segment.kickedDigitalWalk_contains side point).mp contains with first | middle | last
  · have bounds := startKick_bounds unit first
    rcases unit with rfl | rfl
    · have increasing : segment.start.1 ≤ segment.finish.1 := by omega
      have realWide : (3 : ℝ) ≤ (segment.finish.1 : ℝ)-segment.start.1 := by
        exact_mod_cast (show 3 ≤ segment.finish.1-segment.start.1 by omega)
      simp only [RealBoxContains,min_eq_left increasing,max_eq_right increasing]
      norm_num at bounds
      exact ⟨by linarith,by linarith,
        by rw [bounds.2.2]; exact_mod_cast min_le_left segment.start.2 segment.finish.2,
        by rw [bounds.2.2]; exact_mod_cast le_max_left segment.start.2 segment.finish.2⟩
    · have decreasing : segment.finish.1 ≤ segment.start.1 := by omega
      have realWide : (3 : ℝ) ≤ (segment.start.1 : ℝ)-segment.finish.1 := by
        exact_mod_cast (show 3 ≤ segment.start.1-segment.finish.1 by omega)
      simp only [RealBoxContains,min_eq_right decreasing,max_eq_left decreasing]
      norm_num at bounds
      exact ⟨by linarith,by linarith,
        by rw [bounds.2.2]; exact_mod_cast min_le_left segment.start.2 segment.finish.2,
        by rw [bounds.2.2]; exact_mod_cast le_max_left segment.start.2 segment.finish.2⟩
  · have bounds := (segment.kickedSegment side).digitalRoute_box middle
    have horizontal := kickedSegment_horizontal_bounds unit wide middle
    rcases unit with rfl | rfl
    · have increasing : segment.start.1 ≤ segment.finish.1 := by omega
      simp only [RealBoxContains,min_eq_left increasing,max_eq_right increasing]
      exact ⟨by norm_num at horizontal; linarith,by norm_num at horizontal; linarith,
        bounds.2.2.1,bounds.2.2.2⟩
    · have decreasing : segment.finish.1 ≤ segment.start.1 := by omega
      simp only [RealBoxContains,min_eq_right decreasing,max_eq_left decreasing]
      exact ⟨by norm_num at horizontal; linarith,by norm_num at horizontal; linarith,
        bounds.2.2.1,bounds.2.2.2⟩
  · have bounds := finishKick_bounds unit last
    rcases unit with rfl | rfl
    · have increasing : segment.start.1 ≤ segment.finish.1 := by omega
      simp only [RealBoxContains,min_eq_left increasing,max_eq_right increasing]
      have realWide : (3 : ℝ) ≤ (segment.finish.1 : ℝ)-segment.start.1 := by
        exact_mod_cast (show 3 ≤ segment.finish.1-segment.start.1 by omega)
      norm_num at bounds
      exact ⟨by linarith,by linarith,by rw [bounds.2.2]; exact_mod_cast min_le_right segment.start.2 segment.finish.2,
        by rw [bounds.2.2]; exact_mod_cast le_max_right segment.start.2 segment.finish.2⟩
    · have decreasing : segment.finish.1 ≤ segment.start.1 := by omega
      simp only [RealBoxContains,min_eq_right decreasing,max_eq_left decreasing]
      have realWide : (3 : ℝ) ≤ (segment.start.1 : ℝ)-segment.finish.1 := by
        exact_mod_cast (show 3 ≤ segment.start.1-segment.finish.1 by omega)
      norm_num at bounds
      exact ⟨by linarith,by linarith,by rw [bounds.2.2]; exact_mod_cast min_le_right segment.start.2 segment.finish.2,
        by rw [bounds.2.2]; exact_mod_cast le_max_right segment.start.2 segment.finish.2⟩

theorem kickedDigitalRoute_box {segment : GridSegment} {side : Int}
    (unit : side = 1 ∨ side = -1) (wide : 3 ≤ side*(segment.finish.1-segment.start.1))
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (segment.kickedDigitalRoute side) point) :
    segment.RealBoxContains point :=
  kickedDigitalWalk_box unit wide
    (kickedDigitalRoute_contains (by rcases unit with rfl | rfl <;> norm_num) contains)

end LeanTrominoes.GridSegment
