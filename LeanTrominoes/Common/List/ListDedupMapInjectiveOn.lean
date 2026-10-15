/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Deduplication through finite-list injective maps -/

namespace List

/-- Deduplication commutes with a map that is injective on the values actually
presented by the finite source list. -/
theorem dedup_map_of_injective_on
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (mapping : Source → Target) (source : List Source)
    (injectiveOn : ∀ first ∈ source, ∀ second ∈ source,
      mapping first = mapping second → first = second) :
    (source.map mapping).dedup = source.dedup.map mapping := by
  induction source with
  | nil => rfl
  | cons head tail induction =>
      have tailInjective :
          ∀ first ∈ tail, ∀ second ∈ tail,
            mapping first = mapping second → first = second := by
        intro first firstMember second secondMember equal
        exact injectiveOn first (by simp [firstMember])
          second (by simp [secondMember]) equal
      by_cases headMember : head ∈ tail
      · have mappedHeadMember : mapping head ∈ tail.map mapping :=
          List.mem_map.mpr ⟨head, headMember, rfl⟩
        simp [headMember, mappedHeadMember,
          induction tailInjective]
      · have mappedHeadNotMember : mapping head ∉ tail.map mapping := by
          intro mappedHeadMember
          rcases List.mem_map.mp mappedHeadMember with
            ⟨other, otherMember, equal⟩
          have headEqual : head = other :=
            injectiveOn head (by simp) other
              (by simp [otherMember]) equal.symm
          exact headMember (headEqual ▸ otherMember)
        simp [headMember, mappedHeadNotMember,
          induction tailInjective]

end List
