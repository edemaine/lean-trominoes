/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPartialMatching
import LeanTrominoes.BipartiteRouteProjection

/-! # Lifting alternating quotient routes with their actual matched offsets -/
namespace LeanTrominoes.PeriodicBipartite
open BipartiteMatching BlockingPath
variable {L R : Type*} {d : Nat}

namespace PeriodOnePartial
variable {edges : List (Edge L R d)} (matching : PeriodOnePartial edges)
include matching

theorem lift_route (p : Route L R) (alternating : Alternating (QuotientAdj edges) matching.quotient p)
    (z : Lattice d) : ∃ q : Route (L × Lattice d) (R × Lattice d),
    Alternating (Adj edges) matching.partners q ∧ q.first=(p.first,z) ∧ q.map Prod.fst Prod.fst=p := by
  induction alternating generalizing z with
  | @last l r edge free =>
    obtain ⟨e,he,left,right⟩ := edge
    refine ⟨.last (l,z) (r,z+e.offset),Alternating.last ?_ (matching.right_free r free _),rfl,rfl⟩
    exact ⟨e,he,left,right,rfl⟩
  | @cons l r p edge mate rest ih =>
    obtain ⟨e,he,left,right⟩ := edge
    obtain ⟨q,alt,first,project⟩ := ih (z+e.offset-matching.offset p.first)
    refine ⟨.cons (l,z) (r,z+e.offset) q,Alternating.cons ?_ ?_ alt,rfl,?_⟩
    · exact ⟨e,he,left,right,rfl⟩
    · rw [first]
      exact matching.right_at r p.first mate (z+e.offset)
    · simp only [Route.map,project]

end PeriodOnePartial
end LeanTrominoes.PeriodicBipartite
