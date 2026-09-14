/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLAtomGroups

/-! # Separation of subbrick interiors in the infinite lattice -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

def atomOffset (location : Cell) (entry : Atom × Cell) : Cell :=
  Cell.add (origin location) entry.2

def atomMicroOffset (location : Cell) (entry : Atom × Cell) : Cell :=
  Cell.add (brickMicroOrigin location) (entryMicroOffset entry)

theorem atom_micro_offset (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location)) :
    microOrigin (atomMicroOffset location entry) = atomOffset location entry := by
  have alignment := entry_alignment (palette location) entry he
  have brick := brick_micro_origin location
  apply Prod.ext <;> simp only [Prod.ext_iff] at alignment brick
  all_goals dsimp [atomMicroOffset,atomOffset,microOrigin,Cell.add] at *; omega

theorem group_at_image (location : Cell) (entry : Atom × Cell) :
    groupAt location entry = entry.1.group.image (Cell.add (atomMicroOffset location entry)) := by
  simp only [groupAt,entryGroup,Finset.image_image]
  apply Finset.image_congr
  intro c hc
  apply Prod.ext <;> dsimp [atomMicroOffset,Cell.add] <;> omega

/-- A microcell meeting a translated subbrick interior belongs to that subbrick. -/
theorem core_micro_owner (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location)) {c j : Cell}
    (hc : c ∈ entry.1.pattern.region \ entry.1.boundary)
    (hj : Cell.add (atomOffset location entry) c ∈ microRegion j) :
    j ∈ groupAt location entry := by
  let delta := atomMicroOffset location entry
  let k := Cell.sub j delta
  have cancel : Cell.add delta k = j := by
    apply Prod.ext <;> dsimp [k,Cell.add,Cell.sub] <;> omega
  have translated : c ∈ microRegion k := by
    apply (micro_translation delta k c).mp
    rw [cancel,atom_micro_offset palette location he]
    exact hj
  rw [Atom.region_group,Atom.boundary_group] at hc
  have owned := micro_in_group hc translated
  rw [group_at_image]
  exact Finset.mem_image.mpr ⟨k,owned,cancel⟩

/-- A point in a subbrick interior can lie in another subbrick only when
both occurrences are the same. Boundary connector cells are excluded. -/
theorem core_region_owner (palette : Cell → Fin 24) {first second : Cell}
    {a b : Atom × Cell} (ha : a ∈ layout (palette first)) (hb : b ∈ layout (palette second))
    {c : Cell} (hc : c ∈ a.1.pattern.region \ a.1.boundary)
    (other : Cell.add (atomOffset first a) c ∈
      b.1.pattern.region.image (Cell.add (atomOffset second b))) :
    first = second ∧ a = b := by
  change Cell.add (atomOffset first a) c ∈
    b.1.pattern.region.image (Cell.add (Cell.add (origin second) b.2)) at other
  rw [← group_at_region palette second hb] at other
  obtain ⟨j,hj,point⟩ := Finset.mem_biUnion.mp other
  have own := core_micro_owner palette first ha hc point
  have locations := group_locations_eq palette ha hb own hj
  subst second
  exact ⟨rfl,group_entries_eq palette first ha hb own hj⟩

/-- The translated subbrick regions cover every cell of the plane. -/
theorem global_regions_cover (palette : Cell → Fin 24) (c : Cell) :
    ∃ location : Cell, ∃ entry ∈ layout (palette location),
      c ∈ entry.1.pattern.region.image (Cell.add (atomOffset location entry)) := by
  obtain ⟨j,hj⟩ := micro_cover c
  obtain ⟨location,entry,he,owned⟩ := global_groups_cover palette j
  refine ⟨location,entry,he,?_⟩
  change c ∈ entry.1.pattern.region.image (Cell.add (Cell.add (origin location) entry.2))
  rw [← group_at_region palette location he]
  exact Finset.mem_biUnion.mpr ⟨j,owned,hj⟩

end LeanTrominoes.CompletionPattern.LBricks
