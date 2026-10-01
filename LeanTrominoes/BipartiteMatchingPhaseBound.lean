/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! # Arithmetic part of the Hopcroft–Karp phase bound

This module isolates the hypotheses required of a verified blocking-path
algorithm. It is not itself an implementation or a solver certificate.
-/
namespace LeanTrominoes.BipartiteMatching

structure PhaseTrace (vertices phases : Nat) where
  level : Nat → Nat
  deficit : Nat → Nat
  level_step : ∀ i < phases, level i+1 ≤ level (i+1)
  deficit_step : ∀ i < phases, deficit (i+1)+1 ≤ deficit i
  density : ∀ i ≤ phases, deficit i*level i ≤ vertices

namespace PhaseTrace
variable {vertices phases : Nat} (trace : PhaseTrace vertices phases)

theorem level_ge (i : Nat) (hi : i ≤ phases) : i ≤ trace.level i := by
  induction i with
  | zero => omega
  | succ i ih =>
    have previous := ih (by omega)
    have step := trace.level_step i (by omega)
    omega

theorem deficit_drop (i j : Nat) (hij : i ≤ j) (hj : j ≤ phases) :
    trace.deficit j+(j-i) ≤ trace.deficit i := by
  induction j with
  | zero =>
    have equal : i=0 := by omega
    subst i
    simp
  | succ j ih =>
    by_cases equal : i=j+1
    · subst i; simp
    · have previous := ih (by omega) (by omega)
      have step := trace.deficit_step j (by omega)
      omega

/-- Fewer than twice `sqrt(vertices)+1` nonempty blocking phases. -/
theorem phases_bound (trace : PhaseTrace vertices phases) : phases ≤ 2*(Nat.sqrt vertices+1) := by
  let k := Nat.sqrt vertices+1
  by_cases small : phases < k
  · omega
  · have hk : k ≤ phases := by omega
    have level := level_ge trace k hk
    have density := trace.density k hk
    have sq := Nat.lt_succ_sqrt vertices
    have rank : trace.deficit k < k := by
      have product : trace.deficit k*k ≤ vertices :=
        (Nat.mul_le_mul_left _ level).trans density
      have positive : 0 < k := by dsimp [k]; omega
      dsimp [k] at *
      nlinarith
    have drop := deficit_drop trace k phases hk (le_refl _)
    omega

end PhaseTrace
end LeanTrominoes.BipartiteMatching
