/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # The density inequality for large lattice boxes -/
namespace LeanTrominoes.PeriodicBipartite
open Filter Topology

theorem density_le (a b c d : Nat) (bound : ∀ k : Nat, a*k^d ≤ b*(k+c)^d) : a ≤ b := by
  have limit : Tendsto (fun k : Nat => (a : ℝ)*((k : ℝ)/(k+c))^d) atTop (𝓝 (a : ℝ)) := by
    simpa using tendsto_const_nhds.mul ((tendsto_natCast_div_add_atTop (c : ℝ)).pow d)
  have eventual : ∀ᶠ k : Nat in atTop, (a : ℝ)*((k : ℝ)/(k+c))^d ≤ (b : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have kp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have positive : 0 < (k : ℝ)+(c : ℝ) := by positivity
    have one : (a : ℝ)*(k : ℝ)^d ≤ (b : ℝ)*((k : ℝ)+(c : ℝ))^d := by
      exact_mod_cast bound k
    rw [div_pow,← mul_div_assoc]
    exact (div_le_iff₀ (pow_pos positive d)).mpr one
  exact_mod_cast le_of_tendsto limit eventual

end LeanTrominoes.PeriodicBipartite
