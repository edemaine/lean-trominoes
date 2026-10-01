/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingAugment

/-! # Alternating level graphs and shortest-route certificates -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

def levelBuckets (buckets : L → List R) (matching : State L R) (height : L → Nat) (depth : Nat) :
    Buckets L R := fun l => (buckets l).filterMap (fun r => match matching.right r with
      | none => if height l+1=depth then some (r,none) else none
      | some w => if height w=height l+1 then some (r,some w) else none)

theorem mem_levelBuckets (buckets : L → List R) (matching : State L R) (height : L → Nat)
    (depth : Nat) (l : L) (r : R) (next : Option L) :
    (r,next) ∈ levelBuckets buckets matching height depth l ↔ r ∈ buckets l ∧
      match next with
      | none => matching.right r=none ∧ height l+1=depth
      | some w => matching.right r=some w ∧ height w=height l+1 := by
  simp only [levelBuckets,List.mem_filterMap]
  constructor
  · rintro ⟨t,member,eq⟩
    cases mate : matching.right t with
    | none =>
      by_cases layer : height l+1=depth
      · have equal : (t,none)=(r,next) := by simpa [mate,layer] using eq
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
        exact ⟨member,mate,layer⟩
      · simp [mate,layer] at eq
    | some w =>
      by_cases layer : height w=height l+1
      · have equal : (t,some w)=(r,next) := by simpa [mate,layer] using eq
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
        exact ⟨member,mate,layer⟩
      · simp [mate,layer] at eq
  · rintro ⟨member,condition⟩
    refine ⟨r,member,?_⟩
    cases next with
    | none => simp [condition.1,condition.2]
    | some w => simp [condition.1,condition.2]

theorem level_follows_alternating (buckets : L → List R) (matching : State L R) (height : L → Nat)
    (depth : Nat) (p : Route L R) (follows : Follows (levelBuckets buckets matching height depth) p) :
    Alternating (fun l r => r ∈ buckets l) matching p := by
  induction follows with
  | last member =>
    obtain ⟨edge,mate,layer⟩ := (mem_levelBuckets ..).mp member
    exact Alternating.last edge mate
  | cons member rest ih =>
    obtain ⟨edge,mate,layer⟩ := (mem_levelBuckets ..).mp member
    exact Alternating.cons edge mate ih

theorem level_follows_length (buckets : L → List R) (matching : State L R) (height : L → Nat)
    (depth : Nat) (p : Route L R) (follows : Follows (levelBuckets buckets matching height depth) p) :
    height p.first+p.vertices.length=depth := by
  induction follows with
  | @last l r member =>
    obtain ⟨edge,mate,layer⟩ := (mem_levelBuckets ..).mp member
    simpa [Route.first,Route.vertices] using layer
  | @cons l r p member rest ih =>
    obtain ⟨edge,mate,layer⟩ := (mem_levelBuckets ..).mp member
    simp only [Route.first,Route.vertices,List.length_cons]
    omega

theorem level_pairs (buckets : L → List R) (matching : State L R) (height : L → Nat)
    (depth : Nat) (p : Route L R) (follows : Follows (levelBuckets buckets matching height depth) p)
    (l : L) (r : R) (member : (l,r) ∈ routePairs p) :
    r ∈ buckets l ∧ match matching.right r with
      | none => height l+1=depth
      | some w => height w=height l+1 := by
  induction follows with
  | @last a t edge =>
    have equal : (l,r)=(a,t) := by simpa [routePairs] using member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
    obtain ⟨edge,mate,layer⟩ := (mem_levelBuckets ..).mp edge
    exact ⟨edge,by simpa [mate] using layer⟩
  | @cons a t p edge rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      obtain ⟨edge,mate,layer⟩ := (mem_levelBuckets ..).mp edge
      exact ⟨edge,by simpa [mate] using layer⟩
    · exact ih member

structure Labels (buckets : L → List R) (matching : State L R) (height : L → Nat) (depth : Nat) : Prop where
  free : ∀ l, matching.left l=none → height l=0
  arc : ∀ l r, r ∈ buckets l → match matching.right r with
    | none => depth ≤ height l+1
    | some w => height w ≤ height l+1

theorem route_length_lower (buckets : L → List R) (matching : State L R) (height : L → Nat)
    (depth : Nat) (labels : Labels buckets matching height depth) (p : Route L R)
    (alternating : Alternating (fun l r => r ∈ buckets l) matching p) :
    depth ≤ height p.first+p.vertices.length := by
  induction alternating with
  | @last l r edge free =>
    have bound := labels.arc l r edge
    simpa [free,Route.first,Route.vertices] using bound
  | @cons l r p edge mate rest ih =>
    have bound := labels.arc l r edge
    simp only [mate] at bound
    simp only [Route.first,Route.vertices,List.length_cons]
    omega

/-- A tight alternating route uses only the level graph's edges. -/
theorem tight_route_follows (buckets : L → List R) (matching : State L R) (height : L → Nat)
    (depth : Nat) (labels : Labels buckets matching height depth) (p : Route L R)
    (alternating : Alternating (fun l r => r ∈ buckets l) matching p)
    (tight : height p.first+p.vertices.length=depth) :
    Follows (levelBuckets buckets matching height depth) p := by
  induction alternating with
  | @last l r edge free =>
    exact Follows.last ((mem_levelBuckets ..).mpr ⟨edge,free,by simpa [Route.first,Route.vertices] using tight⟩)
  | @cons l r p edge mate rest ih =>
    have bound := labels.arc l r edge
    simp only [mate] at bound
    have tailBound := route_length_lower buckets matching height depth labels p rest
    simp only [Route.first,Route.vertices,List.length_cons] at tight
    have step : height p.first=height l+1 := by omega
    have tailTight : height p.first+p.vertices.length=depth := by omega
    exact Follows.cons ((mem_levelBuckets ..).mpr ⟨edge,mate,step⟩) (ih tailTight)

theorem level_length_le (buckets : L → List R) (matching : State L R) (height : L → Nat)
    (depth : Nat) (l : L) : (levelBuckets buckets matching height depth l).length ≤ (buckets l).length :=
  List.length_filterMap_le _ _

end LeanTrominoes.BipartiteMatching
