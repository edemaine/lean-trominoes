/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentSeparatingAxes

/-! # Algebraic criteria exclude extra contacts at a shared segment endpoint -/
namespace LeanTrominoes.GridSegment

def dot (first second : Cell) : Int := first.1*second.1+first.2*second.2

theorem shared_start_contact {first second : GridSegment} (sameStart : first.start=second.start)
    (rays : cross first.direction second.direction≠0 ∨ dot first.direction second.direction<0)
    {p : ℝ × ℝ} (firstMember : first.RealContains p) (secondMember : second.RealContains p) :
    p=((first.start.1:ℝ),(first.start.2:ℝ)) := by
  obtain ⟨t,tLo,_,tx,ty⟩ := firstMember
  obtain ⟨u,uLo,_,ux,uy⟩ := secondMember
  rw [← sameStart] at ux uy
  have x : t*(first.direction.1:ℝ)=u*(second.direction.1:ℝ) := by
    simp only [direction,Int.cast_sub]
    rw [← sameStart]
    linarith
  have y : t*(first.direction.2:ℝ)=u*(second.direction.2:ℝ) := by
    simp only [direction,Int.cast_sub]
    rw [← sameStart]
    linarith
  have uZero : u=0 := by
    rcases rays with crossed | opposite
    · have crossNonzero : (first.direction.1:ℝ)*(second.direction.2:ℝ)-
          (first.direction.2:ℝ)*(second.direction.1:ℝ)≠0 := by exact_mod_cast crossed
      have product : u*((first.direction.1:ℝ)*(second.direction.2:ℝ)-
          (first.direction.2:ℝ)*(second.direction.1:ℝ))=0 := by
        linear_combination (first.direction.2:ℝ)*x - (first.direction.1:ℝ)*y
      exact (mul_eq_zero.mp product).resolve_right crossNonzero
    · have dotNegative : (first.direction.1:ℝ)*(second.direction.1:ℝ)+
          (first.direction.2:ℝ)*(second.direction.2:ℝ)<0 := by exact_mod_cast opposite
      have identity : t*((first.direction.1:ℝ)^2+(first.direction.2:ℝ)^2)=
          u*((first.direction.1:ℝ)*(second.direction.1:ℝ)+(first.direction.2:ℝ)*(second.direction.2:ℝ)) := by
        linear_combination (first.direction.1:ℝ)*x + (first.direction.2:ℝ)*y
      have nonnegative := mul_nonneg tLo (add_nonneg (sq_nonneg (first.direction.1:ℝ)) (sq_nonneg (first.direction.2:ℝ)))
      by_contra different
      have positive : 0<u := by exact uLo.lt_of_ne' different
      have negative := mul_neg_of_pos_of_neg positive dotNegative
      linarith
  rw [uZero,zero_mul,add_zero] at ux uy
  exact Prod.ext ux uy

end LeanTrominoes.GridSegment
