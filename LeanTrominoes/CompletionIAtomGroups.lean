/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIMicroTranslation
import LeanTrominoes.CompletionIBrickLattice

/-! # The subbricks partition the infinite microcell grid -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def entryMicroOffset (entry : Atom × Cell) : Cell := (entry.2.1 / 18,entry.2.2 / 27)

def entryGroup (entry : Atom × Cell) : Finset Cell :=
  entry.1.group.image (Cell.add (entryMicroOffset entry))

def brickMicroCells : Finset Cell := Finset.Ico (0 : Int) 2 ×ˢ Finset.Ico (0 : Int) 6

theorem entry_alignment (i : Fin 24) :
    ∀ entry ∈ layout i, microOrigin (entryMicroOffset entry) = entry.2 := by
  revert i
  decide +kernel

theorem local_groups_inside (i : Fin 24) :
    ∀ entry ∈ layout i, entryGroup entry ⊆ brickMicroCells := by
  revert i
  decide +kernel

theorem local_groups_cover (i : Fin 24) :
    ∀ m ∈ brickMicroCells, ∃ entry ∈ layout i, m ∈ entryGroup entry := by
  revert i
  decide +kernel

theorem local_groups_disjoint (i : Fin 24) :
    ∀ first ∈ layout i, ∀ second ∈ layout i, first ≠ second →
      Disjoint (entryGroup first) (entryGroup second) := by
  revert i
  decide +kernel

def brickMicroOrigin (location : Cell) : Cell := (2 * location.1 + location.2,6 * location.2)

theorem brick_micro_origin (location : Cell) : microOrigin (brickMicroOrigin location) = origin location := by
  apply Prod.ext <;> dsimp [microOrigin,brickMicroOrigin,origin] <;> omega

def groupAt (location : Cell) (entry : Atom × Cell) : Finset Cell :=
  (entryGroup entry).image (Cell.add (brickMicroOrigin location))

/-- The grouped microcell region is exactly the translated ASCII subbrick. -/
theorem group_at_region (palette : Cell → Fin 24) (location : Cell) {entry : Atom × Cell}
    (he : entry ∈ layout (palette location)) :
    groupRegion (groupAt location entry) =
      entry.1.pattern.region.image (Cell.add (Cell.add (origin location) entry.2)) := by
  unfold groupAt entryGroup
  rw [group_translation,group_translation,← Atom.region_group,
    entry_alignment (palette location) entry he,brick_micro_origin]
  simp only [Finset.image_image]
  apply Finset.image_congr
  intro c hc
  apply Prod.ext <;> dsimp [Cell.add] <;> omega

/-- Every microcell belongs to a subbrick of a uniquely determined physical brick. -/
theorem global_groups_cover (palette : Cell → Fin 24) (m : Cell) :
    ∃ location : Cell, ∃ entry ∈ layout (palette location), m ∈ groupAt location entry := by
  let location : Cell := ((m.1 - m.2 / 6) / 2,m.2 / 6)
  let localCell := Cell.sub m (brickMicroOrigin location)
  have inside : localCell ∈ brickMicroCells := by
    simp only [brickMicroCells,Finset.mem_product,Finset.mem_Ico]
    dsimp [localCell,location,Cell.sub,brickMicroOrigin]
    omega
  obtain ⟨entry,he,hm⟩ := local_groups_cover (palette location) localCell inside
  refine ⟨location,entry,he,Finset.mem_image.mpr ⟨localCell,hm,?_⟩⟩
  apply Prod.ext <;> dsimp [localCell,Cell.add,Cell.sub] <;> omega

/-- Different physical bricks contain disjoint sets of microcell indices. -/
theorem group_locations_eq (palette : Cell → Fin 24) {first second : Cell}
    {a b : Atom × Cell} (ha : a ∈ layout (palette first)) (hb : b ∈ layout (palette second))
    {m : Cell} (hma : m ∈ groupAt first a) (hmb : m ∈ groupAt second b) : first = second := by
  obtain ⟨u,hu,eu⟩ := Finset.mem_image.mp hma
  obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp hmb
  have bu := local_groups_inside (palette first) a ha hu
  have bv := local_groups_inside (palette second) b hb hv
  simp only [brickMicroCells,Finset.mem_product,Finset.mem_Ico] at bu bv
  have eq := eu.trans ev.symm
  simp only [Cell.add,brickMicroOrigin,Prod.mk.injEq] at eq
  apply Prod.ext <;> omega

theorem group_entries_eq (palette : Cell → Fin 24) (location : Cell)
    {a b : Atom × Cell} (ha : a ∈ layout (palette location)) (hb : b ∈ layout (palette location))
    {m : Cell} (hma : m ∈ groupAt location a) (hmb : m ∈ groupAt location b) : a = b := by
  obtain ⟨u,hu,eu⟩ := Finset.mem_image.mp hma
  obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp hmb
  have eq := Cell.add_left_injective (brickMicroOrigin location) (eu.trans ev.symm)
  subst v
  by_contra different
  exact Finset.disjoint_left.mp (local_groups_disjoint (palette location) a ha b hb different) hu hv

end LeanTrominoes.CompletionPattern.IBricks
