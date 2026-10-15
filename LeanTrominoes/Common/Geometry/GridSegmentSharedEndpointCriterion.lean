/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRayContacts

/-! # Endpoint-only contacts exclude rays pointing in the same direction -/
namespace LeanTrominoes.GridSegment

private theorem positive_parallel_x {a b : Cell} (xNonzero : a.1≠0) (bNonzero : b≠(0,0))
    (parallel : cross a b=0) (nonnegative : 0≤dot a b) :
    ∃ factor : ℝ, 0<factor ∧ (b.1:ℝ)=factor*(a.1:ℝ) ∧ (b.2:ℝ)=factor*(a.2:ℝ) := by
  have axNonzero : (a.1:ℝ)≠0 := by exact_mod_cast xNonzero
  have crossZero : (a.1:ℝ)*(b.2:ℝ)-(a.2:ℝ)*(b.1:ℝ)=0 := by exact_mod_cast parallel
  let factor : ℝ := (b.1:ℝ)/(a.1:ℝ)
  have x : (b.1:ℝ)=factor*(a.1:ℝ) := by dsimp [factor]; rw [div_mul_cancel₀ _ axNonzero]
  have y : (b.2:ℝ)=factor*(a.2:ℝ) := by
    apply mul_right_cancel₀ axNonzero
    calc
      _ = (a.2:ℝ)*(b.1:ℝ) := by nlinarith [crossZero]
      _ = _ := by rw [x]; ring
  have factorNonzero : factor≠0 := by
    intro zero
    rw [zero,zero_mul] at x y
    have bx : b.1=0 := by exact_mod_cast x
    have byZero : b.2=0 := by exact_mod_cast y
    exact bNonzero (Prod.ext bx byZero)
  have normPositive : (0:ℝ)<(a.1:ℝ)^2+(a.2:ℝ)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero axNonzero) (sq_nonneg _)
  have realNonnegative : (0:ℝ)≤(a.1:ℝ)*(b.1:ℝ)+(a.2:ℝ)*(b.2:ℝ) := by exact_mod_cast nonnegative
  have productNonnegative : 0≤factor*((a.1:ℝ)^2+(a.2:ℝ)^2) := by rw [x,y] at realNonnegative; nlinarith
  have factorPositive : 0<factor := by
    by_contra notPositive
    have negative : factor<0 := lt_of_le_of_ne (le_of_not_gt notPositive) factorNonzero
    have productNegative := mul_neg_of_neg_of_pos negative normPositive
    linarith
  exact ⟨factor,factorPositive,x,y⟩

theorem positive_parallel {a b : Cell} (aNonzero : a≠(0,0)) (bNonzero : b≠(0,0))
    (parallel : cross a b=0) (nonnegative : 0≤dot a b) :
    ∃ factor : ℝ, 0<factor ∧ (b.1:ℝ)=factor*(a.1:ℝ) ∧ (b.2:ℝ)=factor*(a.2:ℝ) := by
  by_cases xNonzero : a.1≠0
  · exact positive_parallel_x xNonzero bNonzero parallel nonnegative
  · have yNonzero : a.2≠0 := by intro yZero; exact aNonzero (Prod.ext (by omega) yZero)
    have flippedNonzero : (b.2,b.1)≠((0,0):Cell) := by
      intro equal
      exact bNonzero (Prod.ext (congrArg Prod.snd equal) (congrArg Prod.fst equal))
    have flippedCross : cross (a.2,a.1) (b.2,b.1)=0 := by
      unfold cross at parallel ⊢
      nlinarith
    have flippedDot : 0≤dot (a.2,a.1) (b.2,b.1) := by
      simpa only [dot,add_comm] using nonnegative
    obtain ⟨factor,positive,y,x⟩ := positive_parallel_x yNonzero flippedNonzero flippedCross flippedDot
    exact ⟨factor,positive,x,y⟩

theorem ray_criterion_of_contacts_at_endpoints {first second : GridSegment}
    (sameStart : first.start=second.start) (firstNonconstant : first.start≠first.finish)
    (secondNonconstant : second.start≠second.finish)
    (contactOnly : ∀ p : ℝ × ℝ, first.RealContains p → second.RealContains p →
      p=((first.start.1:ℝ),(first.start.2:ℝ)) ∨
        p=((first.finish.1:ℝ),(first.finish.2:ℝ))) :
    cross first.direction second.direction≠0 ∨ dot first.direction second.direction<0 := by
  by_cases nonparallel : cross first.direction second.direction≠0
  · exact Or.inl nonparallel
  · right
    by_contra notOpposite
    have firstDirection : first.direction≠(0,0) := by
      intro equal
      have x := congrArg Prod.fst equal
      have y := congrArg Prod.snd equal
      simp only [direction] at x y
      exact firstNonconstant (Prod.ext (by omega) (by omega))
    have secondDirection : second.direction≠(0,0) := by
      intro equal
      have x := congrArg Prod.fst equal
      have y := congrArg Prod.snd equal
      simp only [direction] at x y
      exact secondNonconstant (Prod.ext (by omega) (by omega))
    obtain ⟨factor,positive,x,y⟩ := positive_parallel firstDirection secondDirection (by omega) (by omega)
    let t : ℝ := min 1 factor/2
    let u : ℝ := t/factor
    have tPositive : 0<t := by dsimp [t]; exact div_pos (lt_min (by norm_num) positive) (by norm_num)
    have tUpper : t≤1 := by have := min_le_left (1:ℝ) factor; dsimp [t]; linarith
    have tStrict : t<1 := by have := min_le_left (1:ℝ) factor; dsimp [t]; linarith
    have tFactor : t≤factor := by have := min_le_right (1:ℝ) factor; dsimp [t]; linarith
    have uBounds : 0≤u ∧ u≤1 :=
      ⟨div_nonneg tPositive.le positive.le,(div_le_one positive).mpr tFactor⟩
    have cancel : u*factor=t := div_mul_cancel₀ _ positive.ne'
    let p : ℝ × ℝ := ((first.start.1:ℝ)+t*(first.direction.1:ℝ),
      (first.start.2:ℝ)+t*(first.direction.2:ℝ))
    have firstMember : first.RealContains p := by
      refine ⟨t,tPositive.le,tUpper,?_,?_⟩ <;> simp [p,direction]
    have secondMember : second.RealContains p := by
      refine ⟨u,uBounds.1,uBounds.2,?_,?_⟩
      · change (first.start.1:ℝ)+t*(first.direction.1:ℝ) =
          (second.start.1:ℝ)+u*((second.finish.1:ℝ)-second.start.1)
        rw [← Int.cast_sub,← show second.direction.1=second.finish.1-second.start.1 from rfl,x,
          ← mul_assoc,cancel,← sameStart]
      · change (first.start.2:ℝ)+t*(first.direction.2:ℝ) =
          (second.start.2:ℝ)+u*((second.finish.2:ℝ)-second.start.2)
        rw [← Int.cast_sub,← show second.direction.2=second.finish.2-second.start.2 from rfl,y,
          ← mul_assoc,cancel,← sameStart]
    rcases contactOnly p firstMember secondMember with equal | equal
    · have zeroX : t*(first.direction.1:ℝ)=0 := by have h := congrArg Prod.fst equal; dsimp [p] at h; linarith
      have zeroY : t*(first.direction.2:ℝ)=0 := by have h := congrArg Prod.snd equal; dsimp [p] at h; linarith
      have xZero : first.direction.1=0 := by exact_mod_cast (mul_eq_zero.mp zeroX).resolve_left tPositive.ne'
      have yZero : first.direction.2=0 := by exact_mod_cast (mul_eq_zero.mp zeroY).resolve_left tPositive.ne'
      exact firstDirection (Prod.ext xZero yZero)
    · have zeroX : (1-t)*(first.direction.1:ℝ)=0 := by
        have h := congrArg Prod.fst equal
        dsimp [p] at h
        simp only [direction,Int.cast_sub] at h ⊢
        nlinarith
      have zeroY : (1-t)*(first.direction.2:ℝ)=0 := by
        have h := congrArg Prod.snd equal
        dsimp [p] at h
        simp only [direction,Int.cast_sub] at h ⊢
        nlinarith
      have nonzero : (1-t:ℝ)≠0 := by linarith
      have xZero : first.direction.1=0 := by exact_mod_cast (mul_eq_zero.mp zeroX).resolve_left nonzero
      have yZero : first.direction.2=0 := by exact_mod_cast (mul_eq_zero.mp zeroY).resolve_left nonzero
      exact firstDirection (Prod.ext xZero yZero)

theorem ray_criterion_of_endpoint_only {first second : GridSegment}
    (sameStart : first.start=second.start) (firstNonconstant : first.start≠first.finish)
    (secondNonconstant : second.start≠second.finish)
    (contactOnly : ∀ p : ℝ × ℝ, first.RealContains p → second.RealContains p →
      p=((first.start.1:ℝ),(first.start.2:ℝ))) :
    cross first.direction second.direction≠0 ∨ dot first.direction second.direction<0 :=
  ray_criterion_of_contacts_at_endpoints sameStart firstNonconstant secondNonconstant
    (fun p firstMember secondMember => Or.inl (contactOnly p firstMember secondMember))

end LeanTrominoes.GridSegment
