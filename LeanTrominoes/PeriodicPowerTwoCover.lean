/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDisplacementGenerators
import LeanTrominoes.PeriodicFiniteCoverReach
import LeanTrominoes.LatticePowerTwoSeparation

/-! # A uniformly bounded finite cover preserves implication contradictions -/
namespace LeanTrominoes.PeriodicLatticeGraph
open ImplicationGraph
variable {V : Type*} {d : Nat} [Fintype V] [DecidableEq V]

def determinantBound (n d B : Nat) : Nat := d.factorial*((2*n+1)*B+1)^d
def implicationPeriod (n d B : Nat) : Nat := coverPeriod (determinantBound n d B)

theorem implicationPeriod_positive (n d B : Nat) : 0 < implicationPeriod n d B := by
  unfold implicationPeriod coverPeriod
  positivity

theorem implicationPeriod_bound (n d B : Nat) :
    implicationPeriod n d B ≤ 2*(d.factorial*((2*n+1)*B+1)^d+1) := coverPeriod_le _

/-- Finite wrapping introduces no new opposite-literal contradiction at this period. -/
theorem cover_contradiction_iff (arcs : List (Arc V d)) (neg : V → V) (involutive : Function.Involutive neg)
    (skew : SkewArcs arcs neg) (B : Nat) (locality : ∀ e ∈ arcs, ∀ i, (e.offset i).natAbs ≤ B) (root : V) :
    let M := implicationPeriod (Fintype.card V) d B
    (CoverReach arcs M (root,0) (neg root,0) ∧ CoverReach arcs M (neg root,0) (root,0)) ↔
    (Reach arcs (root,0) (neg root,0) ∧ Reach arcs (neg root,0) (root,0)) := by
  dsimp only
  let M := implicationPeriod (Fintype.card V) d B
  constructor
  · rintro ⟨forward,backward⟩
    obtain ⟨z,first⟩ := (cover_zero_reach_iff arcs M root (neg root)).mp forward
    obtain ⟨t,second⟩ := (cover_zero_reach_iff arcs M (neg root) root).mp backward
    let R := displacementReach arcs neg involutive skew
    let H := R.displacementGroup first second
    obtain ⟨delta,nonzero,bounded,saturation⟩ := bounded_displacement_saturation arcs neg involutive skew
      B locality root (M • z) (M • t) first second
    have small : delta.natAbs < M := bounded.trans_lt (coverPeriod_gt (determinantBound (Fintype.card V) d B))
    have twice : M • z+M • z ∈ H := R.twice_cross first second
    have member : M • z ∈ H := order_two_separated H delta nonzero saturation
      (Nat.log 2 (determinantBound (Fintype.card V) d B)+1) small (M • z) 0 z H.zero_mem twice (by simp [M,implicationPeriod,coverPeriod])
    exact (R.contradiction_iff first second).mpr member
  · rintro ⟨first,second⟩
    exact ⟨by simpa using reach_wrap arcs M first,by simpa using reach_wrap arcs M second⟩

/-- A fixed-dimensional polynomial bound on the period, valid for a fixed offset bound. -/
theorem implicationPeriod_polynomial (n d B : Nat) :
    implicationPeriod n d B ≤ 2*(d.factorial*(3*B+1)^d+1)*(n+1)^d := by
  have inner : (2*n+1)*B+1 ≤ (3*B+1)*(n+1) := by nlinarith
  have power := Nat.pow_le_pow_left inner d
  have multiplied := Nat.mul_le_mul_left d.factorial power
  rw [mul_pow] at multiplied
  have positive : 1 ≤ (n+1)^d := Nat.one_le_pow _ _ (by omega)
  have bound := implicationPeriod_bound n d B
  nlinarith

end LeanTrominoes.PeriodicLatticeGraph
