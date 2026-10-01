/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingState

/-! # Cardinality and Hall inequalities for finite partial matchings -/
namespace LeanTrominoes.BipartiteMatching
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

def neighborSet (buckets : L → List R) (s : Finset L) : Finset R :=
  s.biUnion (fun l => (buckets l).toFinset)

theorem mem_neighborSet (buckets : L → List R) (s : Finset L) (r : R) :
    r ∈ neighborSet buckets s ↔ ∃ l ∈ s, r ∈ buckets l := by simp [neighborSet]

theorem matching_card (matching : State L R) (consistent : Consistent matching)
    (a : Finset L) (b : Finset R)
    (left : ∀ l ∈ a, ∃ r ∈ b, matching.left l=some r)
    (right : ∀ r ∈ b, ∃ l ∈ a, matching.right r=some l) : a.card=b.card := by
  classical
  choose f member paired using (fun l : {l // l ∈ a} => left l.1 l.2)
  let map : {l // l ∈ a} → {r // r ∈ b} := fun l => ⟨f l,member l⟩
  have inj : Function.Injective map := by
    intro l k equal
    have eq : f l=f k := congrArg Subtype.val equal
    have one := (consistent l.1 (f l)).mp (paired l)
    have two := (consistent k.1 (f k)).mp (paired k)
    rw [← eq] at two
    have same : l.1=k.1 := Option.some.inj (one.symm.trans two)
    exact Subtype.ext same
  have surj : Function.Surjective map := by
    intro r
    obtain ⟨l,hl,mate⟩ := right r.1 r.2
    refine ⟨⟨l,hl⟩,Subtype.ext ?_⟩
    have old := (consistent l r.1).mpr mate
    exact Option.some.inj ((paired ⟨l,hl⟩).symm.trans old)
  have count := Fintype.card_of_bijective ⟨inj,surj⟩
  simpa only [Fintype.card_coe] using count

theorem hall_of_equiv (buckets : L → List R) (f : L ≃ R) (supported : ∀ l, f l ∈ buckets l)
    (s : Finset L) : s.card ≤ (neighborSet buckets s).card := by
  rw [← Finset.card_image_of_injective s f.injective]
  apply Finset.card_le_card
  intro r member
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp member
  exact (mem_neighborSet buckets s _).mpr ⟨l,hl,supported l⟩

end LeanTrominoes.BipartiteMatching
