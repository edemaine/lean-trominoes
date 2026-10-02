/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDominoSolver

/-! # Corollary 5.15: a polynomial indexed arithmetic-RAM budget

The dimension is fixed. Integer arithmetic (including division), comparisons,
and indexed accesses have unit cost, as in the matching solver. This is not a
bit-Turing or Lean VM runtime bound. Matrices and coordinate vectors are stored
in dense arrays; the inverse data is prepared once and reused.

The charges below include coordinate decoding, neighbor generation, the parity
cover and dense reindexing, and the complete finite matching solver. No adjacency
table, coordinate oracle, or matching witness is supplied as input.
-/
namespace LeanTrominoes.Domino
open PeriodicLatticeGraph
variable {n d : Nat}

/-- Number of representatives actually inspected by `firstSome`. -/
def probeVisits {A B : Type*} (probe : A → Option B) : List A → Nat
  | [] => 0
  | v::vs => match probe v with
    | some _ => 1
    | none => 1+probeVisits probe vs

theorem probeVisits_le {A B : Type*} (probe : A → Option B) (vs : List A) :
    probeVisits probe vs ≤ vs.length := by
  induction vs with
  | nil => simp [probeVisits]
  | cons v vs ih => cases h : probe v <;> simp [probeVisits,h]; omega

/-- Two dense matrix-vector products, coordinate subtraction and division,
reconstruction comparison, and loop/index overhead per representative. -/
def probeCharge (d : Nat) : Nat := 20*(d+1)^2

/-- Determinant and all adjugate entries via the permutation formula.
There are `d*d+1` determinants. Each visits `d!` permutations; the generous
quadratic charge includes sign computation and row replacement. For fixed
`d`, permutation enumeration and its table are fixed overhead. -/
def basisCharge (d : Nat) : Nat :=
  (d*d+1)*(d.factorial*(20*(d+1)^2)+20*(d+1)^2)

/-- Every representative and positive coordinate direction generates one query.
Each query scans at most `n` representatives, including unsuccessful searches. -/
def neighborCharge (n d : Nat) : Nat := n*d*(n*(probeCharge d+2)+4)+1

/-- Emit `2^d` cover arcs per original arc, their reverses, and dense indices.
Vector operations cost O(d); vertex enumeration is included even for no edges. -/
def coverCharge (n d e : Nat) : Nat :=
  100*(d+1)*(e+1)*2^d+20*(d+1)*(n+1)*2^d

def BasisData.totalCost (B : BasisData n d) : Nat :=
  basisCharge d+neighborCharge n d+coverCharge n d B.cellArcs.length+
    (PeriodicBipartite.matchingSolver (solverEdges B.cellArcs)).cost+1

/-- The decoder's actual search count obeys the per-query budget. -/
theorem BasisData.decode_search_cost (B : BasisData n d) (I : InverseData d) (x : Cell d) :
    probeVisits (B.probe I x) (List.finRange n)*(probeCharge d+2)+4 ≤
      n*(probeCharge d+2)+4 := by
  have h := probeVisits_le (B.probe I x) (List.finRange n)
  simp only [List.length_finRange] at h
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _

def polynomialCoefficient (d : Nat) : Nat :=
  basisCharge d+((probeCharge d+6)*d+1)+120*(d+1)^2*2^d+
    1000*(2*d*2^d+1)*(2*2^d+1)+1

theorem neighborCharge_bound (n d : Nat) :
    neighborCharge n d ≤ ((probeCharge d+6)*d+1)*(n+1)^2 := by
  unfold neighborCharge
  nlinarith [Nat.zero_le (probeCharge d*d*n),Nat.zero_le (d*n)]

theorem BasisData.coverCharge_bound (B : BasisData n d) :
    coverCharge n d B.cellArcs.length ≤ 120*(d+1)^2*2^d*(n+1)^2 := by
  have edges : B.cellArcs.length+1 ≤ (d+1)*(n+1) := by
    have h := B.cellArcs_size
    nlinarith
  have first := Nat.mul_le_mul_right (2^d) (Nat.mul_le_mul_left (100*(d+1)) edges)
  have square : n+1 ≤ (n+1)^2 := by nlinarith
  have dim : 1 ≤ d+1 := by omega
  unfold coverCharge
  calc
    _ ≤ 120*(d+1)^2*2^d*(n+1) := by nlinarith [Nat.zero_le (20*d*(d+1)*2^d*(n+1))]
    _ ≤ _ := Nat.mul_le_mul_left _ square

theorem BasisData.matchingCost_bound (B : BasisData n d) :
    (PeriodicBipartite.matchingSolver (solverEdges B.cellArcs)).cost ≤
      (1000*(2*d*2^d+1)*(2*2^d+1))*(n+1)^2 := by
  have edges : (solverEdges B.cellArcs).length+1 ≤ (2*d*2^d+1)*(n+1) := by
    rw [solverEdges_length]
    have h := Nat.mul_le_mul_right (2*2^d) B.cellArcs_size
    ring_nf at h ⊢
    omega
  have vertices : Nat.sqrt (n*2^d+n*2^d)+1 ≤ (2*2^d+1)*(n+1) := by
    have h := Nat.sqrt_le_self (n*2^d+n*2^d)
    nlinarith only [h,Nat.zero_le n,Nat.zero_le (2^d)]
  calc
    _ ≤ 1000*((solverEdges B.cellArcs).length+1)*(Nat.sqrt (n*2^d+n*2^d)+1) :=
      PeriodicBipartite.matchingSolver_cost _
    _ ≤ 1000*((2*d*2^d+1)*(n+1))*((2*2^d+1)*(n+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ edges) vertices
    _ = _ := by ring

/-- For every fixed dimension, the complete charged algorithm is quadratic in
its number of fundamental-domain cells, with an explicit dimension-dependent
constant. Coordinates and arbitrary skew period vectors are input data. -/
theorem BasisData.polynomial_time (B : BasisData n d) :
    B.totalCost ≤ polynomialCoefficient d*(n+1)^2 := by
  have neighbors := neighborCharge_bound n d
  have cover := B.coverCharge_bound
  have matching := B.matchingCost_bound
  have one : 1 ≤ (n+1)^2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have setup := Nat.mul_le_mul_left (basisCharge d+1) one
  unfold BasisData.totalCost polynomialCoefficient
  nlinarith

/-- Corollary 5.15, for valid finite fundamental-domain presentations. -/
theorem BasisData.corollary515 (B : BasisData n d) (valid : B.Valid) :
    (B.solve=true ↔ Tileable (B.chart valid).region) ∧
      B.totalCost ≤ polynomialCoefficient d*(n+1)^2 :=
  ⟨B.solve_correct valid,B.polynomial_time⟩

end LeanTrominoes.Domino
