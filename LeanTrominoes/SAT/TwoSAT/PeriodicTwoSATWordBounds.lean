/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATLocalTime
import LeanTrominoes.Computation.RAM.WordBounds

/-! # Word bounds for normalization and explicit finite covers

For fixed dimension, cover sizes and dense vertex indices are polynomial in
`inputSize`, so their signed representation uses O(log(inputSize+2)) bits.
Common input offsets may be arbitrary integers; local differences fit two bits.
These are magnitude bounds, not an instruction-level solver simulation.
-/
namespace LeanTrominoes.PeriodicTwoSAT
variable {n d : ℕ}

/-- Period, coordinate-table size, vertex count, and edge count have a common
polynomial magnitude bound. Dense vertex indices are smaller than the vertex count. -/
theorem cover_magnitudes (formula : Formula (Fin n) d) :
    period (Fin n) d ≤ 2*sizeBound formula ∧
    (period (Fin n) d)^d ≤ sizeBound formula ∧
    n*2*(period (Fin n) d)^d ≤ 2*(sizeBound formula)^2 ∧
    (coverEdges formula (period (Fin n) d)).length ≤ 2*(sizeBound formula)^2 := by
  let W := sizeBound formula
  have variableCount : n≤W := by dsimp [W,sizeBound]; omega
  have clauses : formula.length≤W := by dsimp [W,sizeBound]; omega
  have coordinates : (period (Fin n) d)^d≤W := by dsimp [W,sizeBound]; omega
  have determinant : PeriodicLatticeGraph.determinantBound (2*n) d 2+1≤W := by
    dsimp [W,sizeBound]; omega
  have card : Fintype.card (Signed (Fin n))=2*n := by
    simp [Signed,Nat.mul_comm]
  have periodBound : period (Fin n) d≤2*W := by
    have h := ImplicationGraph.coverPeriod_le (PeriodicLatticeGraph.determinantBound (2*n) d 2)
    simpa [period,PeriodicLatticeGraph.implicationPeriod,card] using h.trans (Nat.mul_le_mul_left 2 determinant)
  have vertices : n*2*(period (Fin n) d)^d≤2*W^2 := by
    nlinarith [Nat.mul_le_mul variableCount coordinates]
  have edges : (coverEdges formula (period (Fin n) d)).length≤2*W^2 := by
    rw [coverEdges_length]
    have arcs := (arcs_length formula).trans (Nat.mul_le_mul_left 2 clauses)
    nlinarith [Nat.mul_le_mul arcs coordinates]
  exact ⟨periodBound,coordinates,vertices,edges⟩

/-- The common finite-cover magnitude budget is polynomial for each fixed d. -/
theorem cover_magnitude_polynomial (formula : Formula (Fin n) d) :
    2*(sizeBound formula)^2 ≤
      (2*(d.factorial*11^d+(2*(d.factorial*11^d+1))^d+3)^2)*
        (inputSize formula)^(2*(d*d+d+1)) := by
  have bound := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (sizeBound_polynomial formula) 2)
  simpa [mul_pow,← pow_mul,Nat.mul_assoc,Nat.mul_comm (d*d+d+1) 2] using bound

/-- Every valid cover-table index fits a logarithmic number of signed bits. -/
theorem cover_index_fits (formula : Formula (Fin n) d)
    (i : Fin (n*2*(period (Fin n) d)^d)) :
    ComplexityAbstract.RAM.Fits (WordBounds.bits (2*(sizeBound formula)^2)) (i.val : ℤ) := by
  apply WordBounds.fits_of_natAbs_le
  simpa using i.isLt.le.trans (cover_magnitudes formula).2.2.1

/-- Subtracting the two input offsets of a local clause produces a two-bit value,
even when their common offset is large. No bound on the common offset is assumed. -/
theorem local_difference_fits (formula : Formula (Fin n) d) (locality : LocalDifferences formula)
    (a b : Literal (Fin n) d) (member : some (a,b)∈formula) (i : Fin d) :
    ComplexityAbstract.RAM.Fits 2 (b.2 i-a.2 i) := by
  have h := locality a b member i
  have abs : ((b.2 i-a.2 i).natAbs : ℤ)≤1 := by exact_mod_cast h
  rw [Int.natCast_natAbs] at abs
  have both := abs_le.mp abs
  exact ⟨by decide,by norm_num; omega,by norm_num; omega⟩

end LeanTrominoes.PeriodicTwoSAT
