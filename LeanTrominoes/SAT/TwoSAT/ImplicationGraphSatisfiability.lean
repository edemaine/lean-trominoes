/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Zorn
import Mathlib.Logic.Relation

/-! # The implication-graph criterion for finite and infinite 2SAT

The proof uses maximal consistent upward-closed sets, so it applies to
infinite graphs without a finiteness or compactness assumption.
-/
namespace LeanTrominoes.ImplicationGraph
variable {A : Type*}

structure SkewReach (A : Type*) where
  neg : A → A
  involutive : Function.Involutive neg
  reach : A → A → Prop
  refl : ∀ a, reach a a
  trans : ∀ {a b c}, reach a b → reach b c → reach a c
  skew : ∀ {a b}, reach a b → reach (neg b) (neg a)

namespace SkewReach
variable (G : SkewReach A)
def ConsistentClosed (T : Set A) : Prop :=
  (∀ a ∈ T, G.neg a ∉ T) ∧ (∀ a ∈ T, ∀ b, G.reach a b → b ∈ T)
def Model (T : Set A) : Prop :=
  (∀ a, G.neg a ∈ T ↔ a ∉ T) ∧ (∀ a ∈ T, ∀ b, G.reach a b → b ∈ T)
def NoContradiction : Prop := ∀ a, ¬ (G.reach a (G.neg a) ∧ G.reach (G.neg a) a)

private theorem extend_consistent (T : Set A) (closed : G.ConsistentClosed T) (a : A)
    (absent : G.neg a ∉ T) (safe : ¬ G.reach a (G.neg a)) :
    G.ConsistentClosed (T ∪ {b | G.reach a b}) := by
  refine ⟨?_,?_⟩
  · intro b member opposite
    rcases member with old | fresh <;> rcases opposite with oldNeg | freshNeg
    · exact closed.1 b old oldNeg
    · exact absent (closed.2 b old _ (by simpa only [G.involutive b] using G.skew freshNeg))
    · have toNeg : G.reach (G.neg b) (G.neg a) := G.skew fresh
      exact absent (closed.2 _ oldNeg _ toNeg)
    · exact safe (G.trans fresh (by simpa only [G.involutive b] using G.skew freshNeg))
  · intro b member c edge
    rcases member with old | fresh
    · exact Or.inl (closed.2 b old c edge)
    · exact Or.inr (G.trans fresh edge)

/-- The usual mutual-reachability criterion remains valid for infinite 2SAT. -/
theorem model_iff : (∃ T, G.Model T) ↔ G.NoContradiction := by
  classical
  constructor
  · rintro ⟨T,model⟩ a ⟨forward,backward⟩
    by_cases truth : a ∈ T
    · exact ((model.1 a).mp (model.2 a truth _ forward)) truth
    · have opposite := (model.1 a).mpr truth
      exact truth (model.2 _ opposite _ backward)
  · intro noContradiction
    obtain ⟨T,maximal⟩ := zorn_subset {T : Set A | G.ConsistentClosed T} (by
      intro chain members ordered
      refine ⟨⋃₀ chain,?_,?_⟩
      · refine ⟨?_,?_⟩
        · intro a ha hna
          obtain ⟨S,hS,ha⟩ := Set.mem_sUnion.mp ha
          obtain ⟨U,hU,hna⟩ := Set.mem_sUnion.mp hna
          rcases ordered.total hS hU with h | h
          · exact (members hU).1 a (h ha) hna
          · exact (members hS).1 a ha (h hna)
        · intro a ha b edge
          obtain ⟨S,hS,ha⟩ := Set.mem_sUnion.mp ha
          exact Set.mem_sUnion.mpr ⟨S,hS,(members hS).2 a ha b edge⟩
      · intro S hS
        exact Set.subset_sUnion_of_mem hS)
    have closed : G.ConsistentClosed T := maximal.1
    have complete (a : A) : a ∈ T ∨ G.neg a ∈ T := by
      by_contra incomplete
      have absent : a ∉ T ∧ G.neg a ∉ T := not_or.mp incomplete
      have insert (b : A) (hb : G.neg b ∉ T) (safe : ¬ G.reach b (G.neg b)) : b ∈ T := by
        have extended := G.extend_consistent T closed b hb safe
        have back : T ∪ {c | G.reach b c} ⊆ T := maximal.2 extended Set.subset_union_left
        exact back (Or.inr (G.refl b))
      by_cases safe : G.reach a (G.neg a)
      · have reverse : ¬ G.reach (G.neg a) (G.neg (G.neg a)) := by
          rw [G.involutive a]
          exact fun h => noContradiction a ⟨safe,h⟩
        have hb : G.neg (G.neg a) ∉ T := by simpa only [G.involutive a] using absent.1
        exact absent.2 (insert _ hb reverse)
      · exact absent.1 (insert a absent.2 safe)
    refine ⟨T,?_,closed.2⟩
    intro a
    constructor
    · intro opposite truth
      exact closed.1 a truth opposite
    · intro absent
      exact (complete a).resolve_left absent

end SkewReach
end LeanTrominoes.ImplicationGraph
