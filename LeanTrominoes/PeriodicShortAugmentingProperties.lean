/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicShortAugmentingPath

/-! # Path simplicity, unmatched forward edges, and the full Lemma 4.5 disjunction -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*}

theorem alternating_target_free (adj : L → R → Prop) (s : State L R) (p : Route L R)
    (alternating : Alternating adj s p) : s.right p.target=none := by
  induction alternating <;> simp_all [Route.target]

theorem alternating_pairs_unmatched (adj : L → R → Prop) (s : State L R) (consistent : Consistent s)
    (p : Route L R) (alternating : Alternating adj s p) (simple : p.vertices.Nodup) :
    ∀ l r, (l,r) ∈ routePairs p → s.left l ≠ some r := by
  classical
  induction alternating with
  | @last a b edge free =>
    intro l r member paired
    have equal : (l,r)=(a,b) := by simpa [routePairs] using member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
    have mate := (consistent l r).mp paired
    rw [free] at mate
    cases mate
  | @cons a b p edge mate rest ih =>
    intro l r member paired
    rcases List.mem_cons.mp member with equal | member
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      have same := (consistent l r).mp paired
      have equal : l=p.first := Option.some.inj (same.symm.trans mate)
      have absent := (List.nodup_cons.mp simple).1
      apply absent
      rw [equal]
      cases p <;> simp [Route.first,Route.vertices]
    · exact ih (List.nodup_cons.mp simple).2 l r member paired

end LeanTrominoes.BipartiteMatching
namespace LeanTrominoes.PeriodicBipartite
open BipartiteMatching BlockingPath
variable {L R : Type*} {d : Nat} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

namespace ShortAugmentingPath
variable {edges : List (Edge L R d)} {matching : PeriodOnePartial edges} (path : ShortAugmentingPath matching)
include path

theorem simple : path.route.allVertices.Nodup := by
  have projected := path.protoSimple
  rw [Route.allVertices_map] at projected
  exact List.Nodup.of_map _ projected

theorem target_free : matching.partners.right path.route.target=none :=
  alternating_target_free (Adj edges) matching.partners path.route path.alternating

omit path [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R] in
private theorem left_nodup {A B : Type*} (p : Route A B) (simple : p.allVertices.Nodup) : p.vertices.Nodup := by
  induction p with
  | last l r => simp [Route.vertices]
  | cons l r p ih =>
    have first := List.nodup_cons.mp simple
    have second := List.nodup_cons.mp first.2
    refine List.nodup_cons.mpr ⟨?_,ih second.2⟩
    intro member
    apply first.1
    exact List.mem_cons.mpr (Or.inr ((Route.inl_mem l p).mpr member))

theorem forward_unmatched : ∀ l r, (l,r) ∈ routePairs path.route → matching.partners.left l ≠ some r :=
  alternating_pairs_unmatched (Adj edges) matching.partners matching.consistent path.route
    path.alternating (left_nodup path.route path.simple)

end ShortAugmentingPath

def PerfectPartial {edges : List (Edge L R d)} (matching : PeriodOnePartial edges) : Prop :=
  Full matching.partners ∧ ∀ r, matching.partners.right r ≠ none


theorem PeriodOnePartial.full_to_perfect {edges : List (Edge L R d)} (matching : PeriodOnePartial edges)
    (balanced : Fintype.card L=Fintype.card R) (full : Full matching.partners) : PerfectPartial matching := by
  classical
  have finiteFull := matching.full_iff.mpr full
  have all (l : L) : ∃ r, matching.quotient.left l=some r := Option.ne_none_iff_exists'.mp (finiteFull l)
  choose f paired using all
  have injective : Function.Injective f := by
    intro l k equal
    have one := (matching.quotient_consistent l (f l)).mp (paired l)
    have two := (matching.quotient_consistent k (f k)).mp (paired k)
    rw [← equal] at two
    exact Option.some.inj (one.symm.trans two)
  have onto := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨injective,balanced⟩).2
  refine ⟨full,?_⟩
  rintro ⟨r,z⟩ free
  obtain ⟨l,equal⟩ := onto r
  have finiteMate : matching.quotient.left l=some r := by simpa [equal] using paired l
  have mate := (matching.quotient_consistent l r).mp finiteMate
  have actual := matching.right_at r l mate z
  rw [free] at actual
  cases actual

/-- Lemma 4.5, with an arbitrary period-one partial matching of the lifted graph. -/
theorem perfect_or_short_augmenting (edges : List (Edge L R d)) (perfect : HasPerfectMatching edges)
    (matching : PeriodOnePartial edges) : PerfectPartial matching ∨ Nonempty (ShortAugmentingPath matching) := by
  classical
  by_cases full : Full matching.partners
  · exact Or.inl (matching.full_to_perfect (quotient_card edges ((perfect_iff_quotient edges).mp perfect)) full)
  · exact Or.inr (short_augmenting_path edges perfect matching full)

end LeanTrominoes.PeriodicBipartite
