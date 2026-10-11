/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentCollinearSeparation
import LeanTrominoes.GridSegmentRealScaling

/-! # Coordinate tubes around integer segments

Integer separating axes control arbitrary points near a segment, rather than
only perturbations of its endpoints. This permits rectilinear rasterization
with a refinement factor linear in the input direction bound.
-/
namespace LeanTrominoes.GridSegment

def RealTubeContains (segment : GridSegment) (radius : ℝ) (point : ℝ × ℝ) : Prop :=
  ∃ original : ℝ × ℝ, segment.RealContains original ∧
    |point.1-original.1| ≤ radius ∧ |point.2-original.2| ≤ radius

theorem RealTubeContains.mono {segment : GridSegment} {firstRadius secondRadius : ℝ} {point : ℝ × ℝ}
    (contains : segment.RealTubeContains firstRadius point) (larger : firstRadius ≤ secondRadius) :
    segment.RealTubeContains secondRadius point := by
  obtain ⟨original,originalContains,x,y⟩ := contains
  exact ⟨original,originalContains,x.trans larger,y.trans larger⟩

theorem RealTubeContains.compose {parent child : GridSegment} {firstRadius secondRadius : ℝ}
    (childBound : ∀ point, child.RealContains point → parent.RealTubeContains firstRadius point)
    {point : ℝ × ℝ} (contains : child.RealTubeContains secondRadius point) :
    parent.RealTubeContains (firstRadius+secondRadius) point := by
  obtain ⟨childPoint,childContains,childX,childY⟩ := contains
  obtain ⟨parentPoint,parentContains,parentX,parentY⟩ := childBound childPoint childContains
  refine ⟨parentPoint,parentContains,?_,?_⟩
  · calc
      _ = |(point.1-childPoint.1)+(childPoint.1-parentPoint.1)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ firstRadius+secondRadius := by linarith
  · calc
      _ = |(point.2-childPoint.2)+(childPoint.2-parentPoint.2)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ firstRadius+secondRadius := by linarith

theorem RealTubeContains.scale {segment : GridSegment} {radius : ℝ} {point : ℝ × ℝ}
    (contains : segment.RealTubeContains radius point) {factor : Int} (nonnegative : 0 ≤ factor) :
    (segment.scale factor).RealTubeContains ((factor : ℝ)*radius)
      ((factor : ℝ)*point.1,(factor : ℝ)*point.2) := by
  obtain ⟨original,⟨t,lower,upper,x,y⟩,nearX,nearY⟩ := contains
  have realNonnegative : (0 : ℝ) ≤ factor := by exact_mod_cast nonnegative
  refine ⟨((factor : ℝ)*original.1,(factor : ℝ)*original.2),⟨t,lower,upper,?_,?_⟩,?_,?_⟩
  · simp only [GridSegment.scale,Cell.scale,Int.cast_mul]
    rw [x]
    ring
  · simp only [GridSegment.scale,Cell.scale,Int.cast_mul]
    rw [y]
    ring
  · change |(factor : ℝ)*point.1-(factor : ℝ)*original.1| ≤ (factor : ℝ)*radius
    rw [← mul_sub,abs_mul,abs_of_nonneg realNonnegative]
    exact mul_le_mul_of_nonneg_left nearX realNonnegative
  · change |(factor : ℝ)*point.2-(factor : ℝ)*original.2| ≤ (factor : ℝ)*radius
    rw [← mul_sub,abs_mul,abs_of_nonneg realNonnegative]
    exact mul_le_mul_of_nonneg_left nearY realNonnegative

theorem realLinearForm_near_bound {bound radius : ℝ} (boundNonnegative : 0 ≤ bound)
    {normal : Cell} (normalBounds : |(normal.1 : ℝ)| ≤ bound ∧ |(normal.2 : ℝ)| ≤ bound)
    {first second : ℝ × ℝ}
    (near : |first.1-second.1| ≤ radius ∧ |first.2-second.2| ≤ radius) :
    |realLinearForm normal first-realLinearForm normal second| ≤ 2*bound*radius := by
  calc
    _ = |(normal.1 : ℝ)*(first.1-second.1)+(normal.2 : ℝ)*(first.2-second.2)| := by
      congr 1
      unfold realLinearForm
      ring
    _ ≤ |(normal.1 : ℝ)*(first.1-second.1)|+|(normal.2 : ℝ)*(first.2-second.2)| := abs_add_le _ _
    _ = |(normal.1 : ℝ)| * |first.1-second.1|+|(normal.2 : ℝ)| * |first.2-second.2| := by
      rw [abs_mul,abs_mul]
    _ ≤ bound*radius+bound*radius := add_le_add
      (mul_le_mul normalBounds.1 near.1 (abs_nonneg _) boundNonnegative)
      (mul_le_mul normalBounds.2 near.2 (abs_nonneg _) boundNonnegative)
    _ = _ := by ring

theorem linearForm_scale (normal point : Cell) (factor : Int) :
    linearForm normal (Cell.scale factor point) = factor*linearForm normal point := by
  unfold linearForm Cell.scale
  ring

theorem realLinearForm_scaled_bounds {factor : Int} (nonnegative : 0 ≤ factor)
    {segment : GridSegment} {point : ℝ × ℝ} (normal : Cell)
    (contains : (segment.scale factor).RealContains point) :
    (factor : ℝ)*(min (linearForm normal segment.start) (linearForm normal segment.finish) : Int) ≤
      realLinearForm normal point ∧
    realLinearForm normal point ≤
      (factor : ℝ)*(max (linearForm normal segment.start) (linearForm normal segment.finish) : Int) := by
  have bounds := realLinearForm_bounds normal contains
  simpa only [scale,linearForm_scale,← mul_min_of_nonneg _ _ nonnegative,
    ← mul_max_of_nonneg _ _ nonnegative,Int.cast_mul] using bounds

theorem StrictlySeparated.scaled_tubes_disjoint {bound factor : Int} {radius : ℝ}
    (boundNonnegative : 0 ≤ bound) (radiusNonnegative : 0 ≤ radius)
    (spacing : 4*(bound : ℝ)*radius < factor)
    {normal : Cell} {first second : GridSegment}
    (separated : StrictlySeparated normal first second)
    (normalBounds : |normal.1| ≤ bound ∧ |normal.2| ≤ bound)
    (point : ℝ × ℝ)
    (firstContains : (first.scale factor).RealTubeContains radius point) :
    ¬(second.scale factor).RealTubeContains radius point := by
  rintro ⟨secondPoint,secondContains,secondX,secondY⟩
  obtain ⟨firstPoint,firstContains,firstX,firstY⟩ := firstContains
  have realBoundNonnegative : (0 : ℝ) ≤ bound := by exact_mod_cast boundNonnegative
  have realNormalBounds : |(normal.1 : ℝ)| ≤ bound ∧ |(normal.2 : ℝ)| ≤ bound := by
    exact_mod_cast normalBounds
  have factorPositive : (0 : ℝ) < factor :=
    lt_of_le_of_lt (by positivity : 0 ≤ 4*(bound : ℝ)*radius) spacing
  have factorNonnegative : 0 ≤ factor := by exact_mod_cast factorPositive.le
  have firstBounds := realLinearForm_scaled_bounds factorNonnegative normal firstContains
  have secondBounds := realLinearForm_scaled_bounds factorNonnegative normal secondContains
  have firstNear := abs_le.mp (realLinearForm_near_bound realBoundNonnegative realNormalBounds ⟨firstX,firstY⟩)
  have secondNear := abs_le.mp (realLinearForm_near_bound realBoundNonnegative realNormalBounds ⟨secondX,secondY⟩)
  have gap : max (linearForm normal first.start) (linearForm normal first.finish)+1 ≤
      min (linearForm normal second.start) (linearForm normal second.finish) := by
    have strict := max_lt_iff.mpr
      ⟨lt_min separated.1 separated.2.1,lt_min separated.2.2.1 separated.2.2.2⟩
    omega
  have realGap : ((max (linearForm normal first.start) (linearForm normal first.finish) : Int) : ℝ)+1 ≤
      (min (linearForm normal second.start) (linearForm normal second.finish) : Int) := by
    exact_mod_cast gap
  have scaledGap := mul_le_mul_of_nonneg_left realGap factorPositive.le
  nlinarith [firstBounds.2,secondBounds.1]

theorem scaled_tubes_disjoint {bound factor : Int} {radius : ℝ}
    (boundPositive : 1 ≤ bound) (radiusNonnegative : 0 ≤ radius)
    (spacing : 4*(bound : ℝ)*radius < factor) {first second : GridSegment}
    (firstBounds : |first.direction.1| ≤ bound ∧ |first.direction.2| ≤ bound)
    (secondBounds : |second.direction.1| ≤ bound ∧ |second.direction.2| ≤ bound)
    (disjoint : ∀ point : ℝ × ℝ, first.RealContains point → ¬second.RealContains point)
    (point : ℝ × ℝ) (contains : (first.scale factor).RealTubeContains radius point) :
    ¬(second.scale factor).RealTubeContains radius point := by
  obtain ⟨normal,normalBounds,separated⟩ := integer_separator boundPositive firstBounds secondBounds disjoint
  exact separated.scaled_tubes_disjoint (by omega) radiusNonnegative spacing normalBounds point contains

theorem RealTubeContains.segment {segment output : GridSegment} {radius : ℝ}
    (start : segment.RealTubeContains radius ((output.start.1 : ℝ),(output.start.2 : ℝ)))
    (finish : segment.RealTubeContains radius ((output.finish.1 : ℝ),(output.finish.2 : ℝ)))
    {point : ℝ × ℝ} (contains : output.RealContains point) :
    segment.RealTubeContains radius point := by
  obtain ⟨first,⟨a,aLower,aUpper,ax,ay⟩,firstX,firstY⟩ := start
  obtain ⟨last,⟨b,bLower,bUpper,bx,byCoord⟩,lastX,lastY⟩ := finish
  obtain ⟨t,tLower,tUpper,px,py⟩ := contains
  let u := (1-t)*a+t*b
  let original : ℝ × ℝ := ((1-t)*first.1+t*last.1,(1-t)*first.2+t*last.2)
  refine ⟨original,⟨u,?_,?_,?_,?_⟩,?_,?_⟩
  · dsimp [u]
    positivity
  · dsimp [u]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) (by linarith : 0 ≤ 1-a),
      mul_nonneg tLower (by linarith : 0 ≤ 1-b)]
  · dsimp [original,u]
    rw [ax,bx]
    ring
  · dsimp [original,u]
    rw [ay,byCoord]
    ring
  · rw [abs_le] at firstX lastX ⊢
    dsimp [original]
    constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) (by linarith : 0 ≤ radius),
      mul_nonneg (by linarith : 0 ≤ 1-t) (by linarith : 0 ≤ radius-((output.start.1 : ℝ)-first.1)),
      mul_nonneg tLower (by linarith : 0 ≤ radius-((output.finish.1 : ℝ)-last.1)),
      mul_nonneg (by linarith : 0 ≤ 1-t) (by linarith : 0 ≤ radius+((output.start.1 : ℝ)-first.1)),
      mul_nonneg tLower (by linarith : 0 ≤ radius+((output.finish.1 : ℝ)-last.1))]
  · rw [abs_le] at firstY lastY ⊢
    dsimp [original]
    constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) (by linarith : 0 ≤ radius),
      mul_nonneg (by linarith : 0 ≤ 1-t) (by linarith : 0 ≤ radius-((output.start.2 : ℝ)-first.2)),
      mul_nonneg tLower (by linarith : 0 ≤ radius-((output.finish.2 : ℝ)-last.2)),
      mul_nonneg (by linarith : 0 ≤ 1-t) (by linarith : 0 ≤ radius+((output.start.2 : ℝ)-first.2)),
      mul_nonneg tLower (by linarith : 0 ≤ radius+((output.finish.2 : ℝ)-last.2))]

end LeanTrominoes.GridSegment
