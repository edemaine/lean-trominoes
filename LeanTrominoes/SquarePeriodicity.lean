/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Periodic
import LeanTrominoes.KeyedPeriodicComplement
import Mathlib.Tactic.Linarith

/-! # Square-period invariance of lattice regions -/

namespace LeanTrominoes

theorem PeriodicRegion.carrier_add_periods_iff (region : PeriodicRegion) (i j : Int) (c : Cell) :
    Cell.add (Cell.add c (Cell.scale i region.period₁)) (Cell.scale j region.period₂) ∈ region.carrier ↔
      c ∈ region.carrier := by
  constructor
  · rintro ⟨base, member, u, v, eq⟩
    refine ⟨base, member, u - i, v - j, ?_⟩
    apply Prod.ext
    · have h := congrArg Prod.fst eq
      dsimp [Cell.add, Cell.scale] at h ⊢
      nlinarith
    · have h := congrArg Prod.snd eq
      dsimp [Cell.add, Cell.scale] at h ⊢
      nlinarith
  · rintro ⟨base, member, u, v, rfl⟩
    refine ⟨base, member, u + i, v + j, ?_⟩
    apply Prod.ext <;> dsimp [Cell.add, Cell.scale] <;> ring

/-- Invariance under both square-lattice period translations. -/
def IsSquarePeriodic (n : Nat) (region : Set Cell) : Prop :=
  ∀ c : Cell, ∀ i j : Int,
    Cell.add ((n : Int) * i, (n : Int) * j) c ∈ region ↔ c ∈ region

theorem PeriodicRegion.isSquarePeriodic (region : PeriodicRegion) (n : Nat)
    (first : region.period₁ = ((n : Int), 0)) (second : region.period₂ = (0, (n : Int))) :
    IsSquarePeriodic n region.carrier := by
  intro c i j
  have h := region.carrier_add_periods_iff i j c
  simpa only [first, second, Cell.add, Cell.scale, Int.mul_zero, Int.add_zero,
    Int.mul_comm, Int.add_comm] using h

theorem IsSquarePeriodic.recenter {n : Nat} {region : Set Cell}
    (periodic : IsSquarePeriodic n region) (offset : Cell) :
    IsSquarePeriodic n {c | Cell.add offset c ∈ region} := by
  intro c i j
  have eq : Cell.add offset (Cell.add ((n : Int) * i, (n : Int) * j) c) =
      Cell.add ((n : Int) * i, (n : Int) * j) (Cell.add offset c) := by
    apply Prod.ext <;> dsimp [Cell.add] <;> omega
  change _ ∈ region ↔ _ ∈ region
  rw [eq]
  exact periodic _ i j

theorem IsSquarePeriodic.union {n : Nat} {s t : Set Cell}
    (hs : IsSquarePeriodic n s) (ht : IsSquarePeriodic n t) : IsSquarePeriodic n (s ∪ t) := by
  intro c i j
  simp only [Set.mem_union, hs c i j, ht c i j]

/-- A square-periodic region is determined by its standard residue mask. -/
theorem IsSquarePeriodic.mem_residue_iff {n : Nat} {region : Set Cell}
    (periodic : IsSquarePeriodic n region) (c : Cell) :
    KeyedPeriodicComplement.residue n c ∈ region ↔ c ∈ region := by
  have eq : Cell.add ((n : Int) * (c.1 / n), (n : Int) * (c.2 / n))
      (KeyedPeriodicComplement.residue n c) = c := by
    have hx := Int.emod_add_mul_ediv c.1 n
    have hy := Int.emod_add_mul_ediv c.2 n
    apply Prod.ext <;> dsimp [Cell.add, KeyedPeriodicComplement.residue] <;> omega
  have h := periodic (KeyedPeriodicComplement.residue n c) (c.1 / n) (c.2 / n)
  rw [eq] at h
  exact h.symm

end LeanTrominoes
