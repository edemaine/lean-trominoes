/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # The fixed-dimensional determinant bound for bounded lattice generators -/
namespace LeanTrominoes.ImplicationGraph
open scoped BigOperators

theorem determinant_bound {d : Nat} (A : Matrix (Fin d) (Fin d) Int) (B : Nat)
    (bounded : ∀ i j, (A i j).natAbs ≤ B) : A.det.natAbs ≤ d.factorial*B^d := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ p : Equiv.Perm (Fin d), ((Equiv.Perm.sign p : Int) * ∏ i, A (p i) i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _p : Equiv.Perm (Fin d), B^d := by
      apply Finset.sum_le_sum
      intro p hp
      have unitAbs : (Equiv.Perm.sign p : Int).natAbs=1 := by
        have unit := (Equiv.Perm.sign p).isUnit
        simpa only [Int.isUnit_iff_natAbs_eq] using unit
      rw [Int.natAbs_mul,unitAbs,one_mul]
      change Int.natAbsHom (∏ i, A (p i) i) ≤ B^d
      rw [map_prod]
      calc
        _ ≤ ∏ i : Fin d, B := Finset.prod_le_prod' (fun i _ => bounded (p i) i)
        _ = B^d := by simp
    _ = d.factorial*B^d := by simp [Fintype.card_perm]

end LeanTrominoes.ImplicationGraph
