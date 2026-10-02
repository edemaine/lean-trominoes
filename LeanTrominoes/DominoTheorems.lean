/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDominoCompletion
import LeanTrominoes.PeriodicDominoSolverCost

/-! # Theorem 5.13 and Corollaries 5.14–5.15

A `Chart V d r` presents a region by finitely many distinct representatives and
`r` independent integer translations in ambient dimension `d`. Tileability is
an exact cover by actual two-cell, face-adjacent domino footprints. Neither
connectivity nor an initially periodic tiling is assumed.

For the executable decision, `BasisData n d` supplies the representatives and
a full-rank integer period matrix. `Valid` expresses that this is a fundamental
domain presentation. The cost model and explicit fixed-dimension polynomial
are specified in `PeriodicDominoSolverCost`.
-/
namespace LeanTrominoes.Domino

/-- Theorem 5.13: double each generator of the original period lattice. -/
theorem theorem513 {V : Type*} [DecidableEq V] [Fintype V] {d r : Nat}
    (C : Chart V d r) (tileable : Tileable C.region) :
    ∃ tiles, IsTiling C.region tiles ∧ PeriodicTiles (doubledPeriod C.period) tiles :=
  C.doubled_tiling tileable

/-- Corollary 5.14: the completion preserves every prefilled domino. -/
theorem corollary514 {V : Type*} [DecidableEq V] [Fintype V] {d r : Nat}
    (C : Chart V d r) (prefill : Set (Finset (Cell d)))
    (periodic : PeriodicTiles C.period prefill) (completion : Completable C.region prefill) :
    ∃ tiles, IsTiling C.region tiles ∧ prefill⊆tiles ∧
      PeriodicTiles (doubledPeriod C.period) tiles :=
  C.doubled_completion prefill periodic completion

/-- Corollary 5.15: executable decision and a complete polynomial RAM budget. -/
theorem corollary515 {n d : Nat} (B : BasisData n d) (valid : B.Valid) :
    (B.solve=true ↔ Tileable (B.chart valid).region) ∧
      B.totalCost ≤ polynomialCoefficient d*(n+1)^2 :=
  B.corollary515 valid

end LeanTrominoes.Domino
