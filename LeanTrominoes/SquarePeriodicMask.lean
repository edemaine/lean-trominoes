/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SquarePeriodicity

/-! # Finite masks for square-periodic regions -/

namespace LeanTrominoes.KeyedPeriodicComplement

/-- The cells of a region in a square fundamental domain. -/
noncomputable def mask (n : Nat) (region : Set Cell) : Polyomino := by
  classical
  exact (square n).filter (fun c => c ∈ region)

theorem mem_mask (n : Nat) (region : Set Cell) (c : Cell) :
    c ∈ mask n region ↔ c ∈ square n ∧ c ∈ region := by
  classical
  simp [mask]

theorem holesRegion_mask {n : Nat} (hn : 0 < n) (region : Set Cell)
    (periodic : IsSquarePeriodic n region) : holesRegion n (mask n region) = region := by
  ext c
  change residue n c ∈ mask n region ↔ c ∈ region
  rw [mem_mask, and_iff_right (residue_mem_square hn c)]
  exact periodic.mem_residue_iff c

end LeanTrominoes.KeyedPeriodicComplement
