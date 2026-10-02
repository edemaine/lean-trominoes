/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTwoSATCore
import LeanTrominoes.PeriodicPowerTwoCover
import LeanTrominoes.PeriodicCoverSymmetry

/-! # The finite contradiction criterion for local periodic 2SAT -/
namespace LeanTrominoes.PeriodicTwoSAT
open PeriodicLatticeGraph ImplicationGraph
variable {V : Type*} {d : Nat} [Fintype V] [DecidableEq V]
def period (V : Type*) [Fintype V] (d : Nat) : Nat := implicationPeriod (Fintype.card (Signed V)) d 2

theorem period_positive : 0 < period V d := implicationPeriod_positive _ _ _

/-- The infinite periodic formula is decided by finite reachability at one copy of each variable. -/
theorem satisfiable_iff_cover (formula : Formula V d) (locality : Local formula) :
    Satisfiable formula ↔ none ∉ formula ∧ ∀ a : V,
      ¬ (CoverReach (arcs formula) (period V d) ((a,true),0) ((a,false),0) ∧
         CoverReach (arcs formula) (period V d) ((a,false),0) ((a,true),0)) := by
  rw [satisfiable_iff_graph,(graph formula).model_iff]
  unfold graph
  rw [infinite_noContradiction_iff (arcs formula) negate negate_involutive (arcs_skew formula)]
  apply and_congr_right
  intro noEmpty
  have card : Fintype.card (Signed V)=2*Fintype.card V := by simp [Signed,Nat.mul_comm]
  have equivalent (a : Signed V) :
      (CoverReach (arcs formula) (period V d) (a,0) (negate a,0) ∧
        CoverReach (arcs formula) (period V d) (negate a,0) (a,0)) ↔
      (Reach (arcs formula) (a,0) (negate a,0) ∧ Reach (arcs formula) (negate a,0) (a,0)) := by
    have h := cover_contradiction_iff (arcs formula) negate negate_involutive
      (arcs_skew formula) 2 (local_arcs formula locality) a
    dsimp only at h
    exact h
  change (∀ a : Signed V, ¬ (Reach (arcs formula) (a,0) (negate a,0) ∧
    Reach (arcs formula) (negate a,0) (a,0))) ↔ _
  constructor
  · intro noContradiction a cover
    have integer := (equivalent (a,true)).mp cover
    exact noContradiction (a,true) integer
  · intro cover a contradiction
    obtain ⟨a,b⟩ := a
    have finite := (equivalent (a,b)).mpr contradiction
    cases b
    · exact cover a finite.symm
    · exact cover a finite

/-- Fixed-dimensional polynomial period bound, without invoking a reachability oracle. -/
theorem period_polynomial : period V d ≤
    2*(d.factorial*7^d+1)*(2*Fintype.card V+1)^d := by
  have h := implicationPeriod_polynomial (Fintype.card (Signed V)) d 2
  simpa [period,Signed,Nat.mul_comm] using h

end LeanTrominoes.PeriodicTwoSAT
