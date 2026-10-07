/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.Dedup

/-! # Computably retain one key for each value in a finite list -/
namespace LeanTrominoes.FiniteKeyDedup

def retain {Key Value : Type*} [DecidableEq Value] (value : Key → Value) (keys : List Key) : List Key :=
  keys.pwFilter fun first last => value first ≠ value last

theorem subset {Key Value : Type*} [DecidableEq Value] (value : Key → Value) (keys : List Key) :
    retain value keys ⊆ keys := List.pwFilter_subset _

theorem values_nodup {Key Value : Type*} [DecidableEq Value] (value : Key → Value) (keys : List Key) :
    ((retain value keys).map value).Nodup :=
  (List.pairwise_pwFilter keys).map value (fun _ _ different => different)

theorem covers_values {Key Value : Type*} [DecidableEq Value] (value : Key → Value) {keys : List Key} {key : Key}
    (member : key ∈ keys) : ∃ representative ∈ retain value keys, value representative = value key := by
  by_contra missing
  have fresh : ∀ other ∈ retain value keys, value key ≠ value other := by
    intro other otherMember equal
    exact missing ⟨other,otherMember,equal.symm⟩
  have negativeTransitive : ∀ {first middle last : Key}, value first ≠ value last → value first ≠ value middle ∨ value middle ≠ value last := by
    intro first middle last different
    by_cases same : value first = value middle
    · right
      intro equal
      exact different (same.trans equal)
    · exact Or.inl same
  have all := (List.forall_mem_pwFilter (R := fun first last => value first ≠ value last) negativeTransitive key keys).mp fresh
  exact all key member rfl

end LeanTrominoes.FiniteKeyDedup
