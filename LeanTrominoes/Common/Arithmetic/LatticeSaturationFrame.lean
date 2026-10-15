/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic

/-! # An integral frame supplies a nonzero saturation multiplier -/
namespace LeanTrominoes.ImplicationGraph
open scoped BigOperators Matrix
abbrev IntegralLattice (d : Nat) := Fin d → Int

/-- A full-rank integral frame, with the active columns in the displacement group.
The adjugate coordinates outside the active columns vanish on the generators. -/
structure SaturationFrame {d : Nat} (generators : Set (IntegralLattice d)) where
  matrix : Matrix (Fin d) (Fin d) Int
  active : Finset (Fin d)
  nonzero : matrix.det ≠ 0
  column_mem : ∀ j ∈ active, (fun i => matrix i j) ∈ AddSubgroup.closure generators
  outside : ∀ g ∈ generators, ∀ j ∉ active, (matrix.adjugate *ᵥ g) j=0

namespace SaturationFrame
variable {d : Nat} {generators : Set (IntegralLattice d)} (frame : SaturationFrame generators)

private theorem outside_closure (g : IntegralLattice d) (member : g ∈ AddSubgroup.closure generators) :
    ∀ j ∉ frame.active, (frame.matrix.adjugate *ᵥ g) j=0 := by
  induction member using AddSubgroup.closure_induction with
  | mem x hx => exact frame.outside x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
    intro j hj
    simp [Matrix.mulVec_add,ihx j hj,ihy j hj]
  | neg x hx ih =>
    intro j hj
    simp [Matrix.mulVec_neg,ih j hj]

/-- Cramer's rule gives a saturation multiplier even when the generator rank is less than d. -/
theorem saturation (z : IntegralLattice d) (c : Int) (nonzero : c ≠ 0)
    (member : c • z ∈ AddSubgroup.closure generators) :
    frame.matrix.det • z ∈ AddSubgroup.closure generators := by
  have outside (j : Fin d) (hj : j ∉ frame.active) : (frame.matrix.adjugate *ᵥ z) j=0 := by
    have vanished := frame.outside_closure (c • z) member j hj
    rw [Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul] at vanished
    exact (mul_eq_zero.mp vanished).resolve_left nonzero
  have cramer := Matrix.mulVec_cramer frame.matrix z
  rw [Matrix.cramer_eq_adjugate_mulVec] at cramer
  have expand : frame.matrix *ᵥ (frame.matrix.adjugate *ᵥ z) =
      ∑ j : Fin d, (frame.matrix.adjugate *ᵥ z) j • (fun i => frame.matrix i j) := by
    ext i
    simp [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,mul_comm]
  rw [← cramer,expand]
  apply AddSubgroup.sum_mem
  intro j hj
  by_cases active : j ∈ frame.active
  · exact (AddSubgroup.closure generators).zsmul_mem (frame.column_mem j active) _
  · rw [outside j active,zero_smul]
    exact (AddSubgroup.closure generators).zero_mem

end SaturationFrame
end LeanTrominoes.ImplicationGraph
