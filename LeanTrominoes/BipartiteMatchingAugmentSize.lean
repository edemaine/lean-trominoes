/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingAugment

/-! # Exact matching-size increase and cost of route rewiring -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

theorem matched_tail (adj : L → R → Prop) (s : State L R) (consistent : Consistent s)
    (p : Route L R) (alternating : Alternating adj s p) (l : L) (member : l ∈ p.vertices.tail) :
    ∃ r, s.left l=some r := by
  induction alternating with
  | last edge free => simp [Route.vertices] at member
  | @cons a r p edge mate rest ih =>
    have inside : l ∈ p.vertices := member
    have cases : l=p.first ∨ l ∈ p.vertices.tail := by
      cases p <;> simpa [Route.vertices,Route.first] using inside
    rcases cases with equal | tail
    · subst l; exact ⟨r,(consistent _ _).mpr mate⟩
    · exact ih tail

theorem route_written (s : State L R) (p : Route L R) (simple : p.vertices.Nodup)
    (l : L) (member : l ∈ p.vertices) : ∃ r, (applyRoute s p).left l=some r := by
  rw [← routePairs_fst] at member
  obtain ⟨pair,inside,equal⟩ := List.mem_map.mp member
  obtain ⟨a,r⟩ := pair
  change a=l at equal
  subst a
  exact ⟨r,applyRoute_left_write s p simple l r inside⟩

theorem applyRoute_domain (adj : L → R → Prop) (s : State L R) (consistent : Consistent s)
    (p : Route L R) (alternating : Alternating adj s p) (simple : p.vertices.Nodup) :
    domain (applyRoute s p)=insert p.first (domain s) := by
  ext l
  by_cases root : l=p.first
  · subst l
    obtain ⟨r,paired⟩ := route_written s p simple p.first p.first_mem
    simp [domain,paired]
  · by_cases inside : l ∈ p.vertices
    · have tail : l ∈ p.vertices.tail := by
        cases p <;> simp_all [Route.vertices,Route.first]
      obtain ⟨r,old⟩ := matched_tail adj s consistent p alternating l tail
      obtain ⟨t,new⟩ := route_written s p simple l inside
      simp [domain,root,old,new]
    · have same := applyRoute_left_outside s p l inside
      simp [domain,root,same]

theorem applyRoute_size (adj : L → R → Prop) (s : State L R) (consistent : Consistent s)
    (p : Route L R) (alternating : Alternating adj s p) (simple : p.vertices.Nodup)
    (rootFree : s.left p.first=none) : size (applyRoute s p)=size s+1 := by
  have absent : p.first ∉ domain s := by simp [domain,rootFree]
  simp [size,applyRoute_domain adj s consistent p alternating simple,absent]

/-- The charge covers both inverse-array updates and stack control. -/
def executeRoute (s : State L R) : Route L R → State L R × Nat
  | .last l r => (pair s l r,8)
  | .cons l r p =>
    let later := executeRoute (unpair s p.first r) p
    (pair later.1 l r,16+later.2)

theorem executeRoute_state (s : State L R) (p : Route L R) : (executeRoute s p).1=applyRoute s p := by
  induction p generalizing s <;> simp_all [executeRoute,applyRoute]

theorem executeRoute_cost (s : State L R) (p : Route L R) : (executeRoute s p).2 ≤ 16*p.vertices.length := by
  induction p generalizing s with
  | last l r => simp [executeRoute,Route.vertices]
  | cons l r p ih =>
    have next := ih (unpair s p.first r)
    simp only [executeRoute,Route.vertices,List.length_cons]
    omega

end LeanTrominoes.BipartiteMatching
