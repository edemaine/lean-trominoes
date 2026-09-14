/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLAssembly

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

theorem boundary_outside_micro {s : Finset Cell} {c : Cell} (hc : c ∈ groupBoundary s) :
    ∃ j : Cell, j ∉ s ∧ c ∈ microRegion j := by
  obtain ⟨i,hi,hc⟩ := Finset.mem_biUnion.mp hc
  rcases Finset.mem_union.mp hc with top | bottom
  · split_ifs at top with member
    · simp at top
    · refine ⟨(i.1,i.2 - 1),member,?_⟩
      rw [mem_microRegion]
      simp only [portals,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff] at top
      unfold MemberAt
      dsimp
      omega
  · split_ifs at bottom with member
    · simp at bottom
    · refine ⟨(i.1,i.2 + 1),member,?_⟩
      rw [mem_microRegion]
      simp only [portals,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff] at bottom
      unfold MemberAt
      dsimp
      omega

/-- A boundary point of a subbrick always belongs to a different subbrick as well. -/
theorem boundary_neighbor {palette : Cell → Fin 24} (o : Occurrence palette) {c : Cell}
    (hc : c ∈ o.entry.1.boundary) :
    ∃ other : Occurrence palette, other ≠ o ∧
      Cell.add (atomOffset o.location o.entry) c ∈ regionAt other.location other.entry := by
  rw [Atom.boundary_group] at hc
  obtain ⟨j,absent,point⟩ := boundary_outside_micro hc
  let delta := atomMicroOffset o.location o.entry
  let k := Cell.add delta j
  have translated : Cell.add (atomOffset o.location o.entry) c ∈ microRegion k := by
    rw [← atom_micro_offset palette o.location o.member]
    exact (micro_translation delta j c).mpr point
  obtain ⟨location,entry,he,owned⟩ := global_groups_cover palette k
  let other : Occurrence palette := ⟨location,entry,he⟩
  refine ⟨other,?_,?_⟩
  · intro eq
    have localOwned : k ∈ groupAt o.location o.entry := by
      change k ∈ groupAt other.location other.entry at owned
      rwa [eq] at owned
    rw [group_at_image] at localOwned
    obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp localOwned
    have same : i = j := Cell.add_left_injective delta eq
    exact absent (same ▸ hi)
  · change Cell.add (atomOffset o.location o.entry) c ∈
      entry.1.pattern.region.image (Cell.add (Cell.add (origin location) entry.2))
    rw [← group_at_region palette location he]
    exact Finset.mem_biUnion.mpr ⟨k,owned,translated⟩

/-- Two shared-region states suffice to cover any omitted boundary cell. -/
def SeamCompatible {palette : Cell → Fin 24} (outside : Occurrence palette → Finset Cell) : Prop :=
  ∀ a b : Occurrence palette, a ≠ b → ∀ c : Cell,
    c ∈ regionAt a.location a.entry → c ∈ regionAt b.location b.entry →
      (c ∈ stateTarget a (outside a) ↔ c ∉ stateTarget b (outside b))

/-- Local connector agreement turns realizable states into a partition; no
extra global covering assumption is needed. -/
theorem compatible_of_seams {palette : Cell → Fin 24}
    {outside : Occurrence palette → Finset Cell}
    (localStates : ∀ o, outside o ⊆ o.entry.1.boundary ∧ o.entry.1.pattern.Completable (outside o))
    (seams : SeamCompatible outside) : CompatibleStates palette outside := by
  refine ⟨localStates,?_⟩
  intro c
  have existsOwner : ∃ o : Occurrence palette, c ∈ stateTarget o (outside o) := by
    obtain ⟨location,entry,he,inside⟩ := global_regions_cover palette c
    let o : Occurrence palette := ⟨location,entry,he⟩
    by_cases assigned : c ∈ stateTarget o (outside o)
    · exact ⟨o,assigned⟩
    · obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp inside
      have omitted : d ∈ outside o := by
        by_contra notOmitted
        exact assigned (Finset.mem_image.mpr ⟨d,Finset.mem_sdiff.mpr ⟨hd,notOmitted⟩,eq⟩)
      obtain ⟨other,different,neighbor⟩ := boundary_neighbor o ((localStates o).1 omitted)
      change Cell.add (atomOffset location entry) d ∈ regionAt other.location other.entry at neighbor
      rw [eq] at neighbor
      have complement := seams other o different c neighbor inside
      exact ⟨other,complement.mpr assigned⟩
  obtain ⟨o,ho⟩ := existsOwner
  refine ⟨o,ho,?_⟩
  intro other hc
  by_contra different
  have subset (p : Occurrence palette) : stateTarget p (outside p) ⊆ regionAt p.location p.entry :=
    Finset.image_subset_image Finset.sdiff_subset
  exact (seams other o different c (subset other hc) (subset o ho)).mp hc ho

end LeanTrominoes.CompletionPattern.LBricks
