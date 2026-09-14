/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIMicroGeometry
import LeanTrominoes.CompletionIRegionGeometry

/-! # Grouping closed microcells into subbricks -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def groupRegion (s : Finset Cell) : Finset Cell := s.biUnion microRegion

def portals (i : Cell) (row : Int) : Finset Cell :=
  {(18 * i.1 + 5,27 * row),(18 * i.1 + 14,27 * row)}

def groupBoundary (s : Finset Cell) : Finset Cell := s.biUnion fun i =>
  (if (i.1,i.2 - 1) ∈ s then ∅ else portals i i.2) ∪
  (if (i.1,i.2 + 1) ∈ s then ∅ else portals i (i.2 + 1))

/-- A point in the group's interior cannot belong to an outside microcell. -/
theorem micro_in_group {s : Finset Cell} {j c : Cell}
    (hc : c ∈ groupRegion s \ groupBoundary s) (hj : c ∈ microRegion j) : j ∈ s := by
  obtain ⟨i,hi,hic⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hc).1
  have notBoundary := (Finset.mem_sdiff.mp hc).2
  rcases micro_overlap hic hj with eq | ⟨hx,px,above | below⟩
  · exact eq ▸ hi
  · by_contra absent
    have eq : j = (i.1,i.2 + 1) := by
      apply Prod.ext <;> dsimp <;> omega
    have missing : (i.1,i.2 + 1) ∉ s := by rwa [← eq]
    apply notBoundary
    apply Finset.mem_biUnion.mpr
    refine ⟨i,hi,Finset.mem_union.mpr (Or.inr ?_)⟩
    rw [if_neg missing]
    simp only [portals,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff]
    omega
  · by_contra absent
    have eq : j = (i.1,i.2 - 1) := by
      apply Prod.ext <;> dsimp <;> omega
    have missing : (i.1,i.2 - 1) ∉ s := by rwa [← eq]
    apply notBoundary
    apply Finset.mem_biUnion.mpr
    refine ⟨i,hi,Finset.mem_union.mpr (Or.inl ?_)⟩
    rw [if_neg missing]
    simp only [portals,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff]
    omega

theorem group_core_disjoint {s t : Finset Cell} (separate : Disjoint s t) :
    Disjoint (groupRegion s \ groupBoundary s) (groupRegion t) := by
  apply Finset.disjoint_left.mpr
  intro c hs ht
  obtain ⟨j,hj,hjc⟩ := Finset.mem_biUnion.mp ht
  exact Finset.disjoint_left.mp separate (micro_in_group hs hjc) hj

def Atom.group : Atom → Finset Cell
  | .copy => {(0,0),(1,0),(0,1),(1,1)}
  | .clause => {(0,0),(1,0)}
  | _ => {(0,0)}

theorem Atom.region_group (a : Atom) : a.pattern.region = groupRegion a.group := by
  ext c
  rw [a.mem_region]
  cases a <;>
    simp only [Atom.group,groupRegion,Finset.biUnion_insert,Finset.singleton_biUnion,
      Finset.mem_union,mem_microRegion]
  all_goals
    dsimp [CompletionGuardedShape.Member,Atom.width,Atom.height,MemberAt]
    omega

theorem Atom.boundary_group (a : Atom) : a.boundary = groupBoundary a.group := by
  cases a <;> decide +kernel

end LeanTrominoes.CompletionPattern.IBricks
