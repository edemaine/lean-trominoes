/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingState
import LeanTrominoes.BlockingPathSemantics

/-! # Rewiring a partial matching along an alternating route -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

def routeLabels : Route L R → List R
  | .last _ r => [r]
  | .cons _ r p => r::routeLabels p

def routePairs : Route L R → List (L × R)
  | .last l r => [(l,r)]
  | .cons l r p => (l,r)::routePairs p

theorem routePairs_fst (p : Route L R) : (routePairs p).map Prod.fst=p.vertices := by
  induction p <;> simp_all [routePairs,Route.vertices]
theorem routePairs_snd (p : Route L R) : (routePairs p).map Prod.snd=routeLabels p := by
  induction p <;> simp_all [routePairs,routeLabels]

def applyRoute (s : State L R) : Route L R → State L R
  | .last l r => pair s l r
  | .cons l r p => pair (applyRoute (unpair s p.first r) p) l r

inductive Alternating (adj : L → R → Prop) (s : State L R) : Route L R → Prop
  | last {l r} : adj l r → s.right r=none → Alternating adj s (.last l r)
  | cons {l r p} : adj l r → s.right r=some p.first → Alternating adj s p →
      Alternating adj s (.cons l r p)

theorem alternating_right_congr (adj : L → R → Prop) (s t : State L R) (p : Route L R)
    (same : ∀ r ∈ routeLabels p, t.right r=s.right r) (h : Alternating adj s p) : Alternating adj t p := by
  induction h with
  | @last l r edge free => exact Alternating.last edge (by rw [same r (by simp [routeLabels])]; exact free)
  | @cons l r p edge mate rest ih =>
    exact Alternating.cons edge (by rw [same r (by simp [routeLabels])]; exact mate)
      (ih (fun r hr => same r (List.mem_cons.mpr (Or.inr hr))))

theorem label_classification (adj : L → R → Prop) (s : State L R) (p : Route L R)
    (h : Alternating adj s p) (r : R) (member : r ∈ routeLabels p) :
    s.right r=none ∨ ∃ l ∈ p.vertices.tail, s.right r=some l := by
  induction h with
  | @last l t edge free =>
    have equal : r=t := by simpa [routeLabels] using member
    subst r
    exact Or.inl free
  | @cons l t p edge mate rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst r
      exact Or.inr ⟨p.first,p.first_mem,mate⟩
    · rcases ih member with free | ⟨w,hw,mate⟩
      · exact Or.inl free
      · exact Or.inr ⟨w,List.mem_of_mem_tail hw,mate⟩

theorem first_not_tail (p : Route L R) (nodup : p.vertices.Nodup) : p.first ∉ p.vertices.tail := by
  cases p with
  | last l r => simp [Route.vertices]
  | cons l r p => exact (List.nodup_cons.mp nodup).1

theorem labels_nodup (adj : L → R → Prop) (s : State L R) (p : Route L R)
    (h : Alternating adj s p) (nodup : p.vertices.Nodup) : (routeLabels p).Nodup := by
  induction h with
  | last edge free => simp [routeLabels]
  | @cons l r p edge mate rest ih =>
    have notMem : r ∉ routeLabels p := by
      intro member
      rcases label_classification adj s p rest r member with free | ⟨w,hw,other⟩
      · simp_all
      · have equal : w=p.first := by simpa [mate] using other.symm
        exact first_not_tail p (List.nodup_cons.mp nodup).2 (equal ▸ hw)
    exact List.nodup_cons.mpr ⟨notMem,ih (List.nodup_cons.mp nodup).2⟩

theorem applyRoute_left_outside (s : State L R) (p : Route L R) (l : L) (outside : l ∉ p.vertices) :
    (applyRoute s p).left l=s.left l := by
  induction p generalizing s with
  | last a r =>
    have ne : l ≠ a := by simpa [Route.vertices] using outside
    simp [applyRoute,pair,ne]
  | cons a r p ih =>
    have split : l ≠ a ∧ l ∉ p.vertices := by simpa [Route.vertices] using outside
    have ne := split.1
    have tail := split.2
    have next : l ≠ p.first := by intro eq; subst l; exact tail p.first_mem
    simp only [applyRoute,pair,Function.update_of_ne ne]
    rw [ih _ tail]
    simp [unpair,next]

theorem applyRoute_right_outside (s : State L R) (p : Route L R) (r : R) (outside : r ∉ routeLabels p) :
    (applyRoute s p).right r=s.right r := by
  induction p generalizing s with
  | last l t =>
    have ne : r ≠ t := by simpa [routeLabels] using outside
    simp [applyRoute,pair,ne]
  | cons l t p ih =>
    have split : r ≠ t ∧ r ∉ routeLabels p := by simpa [routeLabels] using outside
    have ne := split.1
    have tail := split.2
    simp only [applyRoute,pair,Function.update_of_ne ne]
    rw [ih _ tail]
    simp [unpair,ne]


theorem applyRoute_left_write (s : State L R) (p : Route L R) (nodup : p.vertices.Nodup)
    (l : L) (r : R) (member : (l,r) ∈ routePairs p) : (applyRoute s p).left l=some r := by
  induction p generalizing s with
  | last a t =>
    have eq : (l,r)=(a,t) := by simpa [routePairs] using member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    simp [applyRoute,pair]
  | cons a t p ih =>
    rcases List.mem_cons.mp member with equal | member
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      simp [applyRoute,pair]
    · have tail := (List.nodup_cons.mp nodup).2
      have memL : l ∈ p.vertices := by rw [← routePairs_fst]; exact List.mem_map.mpr ⟨(l,r),member,rfl⟩
      have ne : l ≠ a := by intro eq; subst l; exact (List.nodup_cons.mp nodup).1 memL
      simpa [applyRoute,pair,ne] using ih (unpair s p.first t) tail member

theorem applyRoute_right_write (s : State L R) (p : Route L R) (nodup : (routeLabels p).Nodup)
    (l : L) (r : R) (member : (l,r) ∈ routePairs p) : (applyRoute s p).right r=some l := by
  induction p generalizing s with
  | last a t =>
    have eq : (l,r)=(a,t) := by simpa [routePairs] using member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    simp [applyRoute,pair]
  | cons a t p ih =>
    rcases List.mem_cons.mp member with equal | member
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      simp [applyRoute,pair]
    · have tail := (List.nodup_cons.mp nodup).2
      have memR : r ∈ routeLabels p := by rw [← routePairs_snd]; exact List.mem_map.mpr ⟨(l,r),member,rfl⟩
      have ne : r ≠ t := by intro eq; subst r; exact (List.nodup_cons.mp nodup).1 memR
      simpa [applyRoute,pair,ne] using ih (unpair s p.first t) tail member

/-- Rewiring preserves the matching and adds one matched left vertex. -/
theorem applyRoute_correct (adj : L → R → Prop) (s : State L R) (p : Route L R)
    (consistent : Consistent s) (supported : Supported adj s) (alternating : Alternating adj s p)
    (simple : p.vertices.Nodup) (rootFree : s.left p.first=none) :
    Consistent (applyRoute s p) ∧ Supported adj (applyRoute s p) := by
  induction p generalizing s with
  | last l r =>
    cases alternating with
    | last edge free => exact ⟨pair_consistent s consistent l r rootFree free,pair_supported adj s supported l r edge⟩
  | cons l r p ih =>
    cases alternating with
    | cons edge mate rest =>
      have paired := (consistent p.first r).mpr mate
      have noLabel : r ∉ routeLabels p := by
        intro member
        rcases label_classification adj s p rest r member with free | ⟨w,hw,other⟩
        · simp_all
        · have equal : w=p.first := by simpa [mate] using other.symm
          exact first_not_tail p (List.nodup_cons.mp simple).2 (equal ▸ hw)
      have nextAlternating : Alternating adj (unpair s p.first r) p :=
        alternating_right_congr adj s _ p (fun t ht => by
          have ne : t ≠ r := by intro eq; subst t; exact noLabel ht
          simp [unpair,ne]) rest
      obtain ⟨nextConsistent,nextSupported⟩ := ih (unpair s p.first r)
        (unpair_consistent s consistent p.first r paired) (unpair_supported adj s supported p.first r)
        nextAlternating (List.nodup_cons.mp simple).2 (by simp [unpair])
      have freeL : (applyRoute (unpair s p.first r) p).left l=none := by
        rw [applyRoute_left_outside _ p l (List.nodup_cons.mp simple).1]
        have ne : l ≠ p.first := by intro eq; exact (List.nodup_cons.mp simple).1 (eq ▸ p.first_mem)
        change Function.update s.left p.first none l=none
        rw [Function.update_of_ne ne]
        exact rootFree
      have freeR : (applyRoute (unpair s p.first r) p).right r=none := by
        rw [applyRoute_right_outside _ p r noLabel]
        simp [unpair]
      exact ⟨pair_consistent _ nextConsistent l r freeL freeR,pair_supported adj _ nextSupported l r edge⟩

end LeanTrominoes.BipartiteMatching
