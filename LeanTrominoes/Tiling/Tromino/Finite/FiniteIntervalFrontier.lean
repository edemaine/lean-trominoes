/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # The first free point beyond a finite occupied prefix -/
namespace LeanTrominoes.FiniteInterval

def upper (s : Finset Int) (b : Int) : Int := (insert b s).max' (by simp)
def lower (s : Finset Int) (a : Int) : Int := (insert a s).min' (by simp)

theorem le_upper (s : Finset Int) (b : Int) : b≤upper s b :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)
theorem lower_le (s : Finset Int) (a : Int) : lower s a≤a :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem free_above (s : Finset Int) (b z : Int)
    (initial : ∀ y∈s, ∀ w, b<w → w≤y → w∈s) (outside : b<z) :
    z∉s ↔ upper s b<z := by
  constructor
  · intro free
    have hm := Finset.max'_mem (insert b s) (by simp)
    change upper s b∈insert b s at hm
    rcases Finset.mem_insert.mp hm with equal|inside
    · omega
    · by_contra h
      exact free (initial _ inside z outside (by omega))
  · intro after inside
    have bound : z≤upper s b := Finset.le_max' _ _ (Finset.mem_insert_of_mem inside)
    omega

theorem free_below (s : Finset Int) (a z : Int)
    (initial : ∀ y∈s, ∀ w, w<a → y≤w → w∈s) (outside : z<a) :
    z∉s ↔ z<lower s a := by
  constructor
  · intro free
    have hm := Finset.min'_mem (insert a s) (by simp)
    change lower s a∈insert a s at hm
    rcases Finset.mem_insert.mp hm with equal|inside
    · omega
    · by_contra h
      exact free (initial _ inside z outside (by omega))
  · intro before inside
    have bound : lower s a≤z := Finset.min'_le _ _ (Finset.mem_insert_of_mem inside)
    omega

end LeanTrominoes.FiniteInterval
