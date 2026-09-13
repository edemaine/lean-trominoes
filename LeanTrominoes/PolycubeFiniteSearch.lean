/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubePrescribedCompactness
import LeanTrominoes.ComputableSearch
import LeanTrominoes.PlaneTilingFiniteSearch

/-! # Finite obstructions for tiling by two arbitrary finite polycubes in a prescribed voxel region -/

namespace LeanTrominoes.VoxelTilingSearch

attribute [local instance] Classical.propDecidable

abbrev Input := List Voxel × List Voxel

def tileList (input : Input) (kind : Bool) : List Voxel := if kind then input.2 else input.1

def tiles (input : Input) : Bool → Polycube := fun kind => (tileList input kind).toFinset

noncomputable def symmetryList : List CubeSymmetry := Finset.univ.toList

noncomputable def candidates (input : Input) (c : Voxel) : List (VoxelPlacement Bool) :=
  [false, true].flatMap fun kind => symmetryList.flatMap fun symmetry =>
    (tileList input kind).map fun q => ⟨kind, symmetry, Voxel.sub c (symmetry.act q)⟩

theorem mem_candidates (input : Input) (c : Voxel) (p : VoxelPlacement Bool) :
    p ∈ candidates input c ↔ c ∈ p.cells (tiles input) := by
  simp only [candidates, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨k, _, s, _, q, hq, rfl⟩
    rw [VoxelPlacement.mem_cells_iff]
    refine ⟨q, List.mem_toFinset.mpr hq, ?_⟩
    exact Voxel.sub_add _ _
  · rw [VoxelPlacement.mem_cells_iff]
    rintro ⟨q, hq, eq⟩
    refine ⟨p.kind, by cases p.kind <;> simp,
      p.symmetry, ?_, q, List.mem_toFinset.mp hq, ?_⟩
    · simp [symmetryList]
    · apply VoxelPlacement.ext
      · rfl
      · rfl
      · simp only [Voxel.add, Cell.add, Prod.ext_iff] at eq
        simp only [Voxel.sub, Cell.sub, Prod.ext_iff]
        exact ⟨⟨by omega, by omega⟩, by omega⟩

def InBox (r : Nat) (c : Voxel) : Prop :=
  LeanWang.InBox r c.1 ∧ LeanWang.InBox r (c.2, 0)

def boxVoxelList (r : Nat) : List Voxel :=
  (TrominoAssignment.boxCellList r).flatMap fun xy =>
    (TrominoAssignment.boxCellList r).map fun z => (xy, z.1)

theorem mem_boxVoxelList (r : Nat) (c : Voxel) : c ∈ boxVoxelList r ↔ InBox r c := by
  simp only [boxVoxelList, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨xy, hxy, z, hz, rfl⟩
    have hz := (TrominoAssignment.mem_boxCellList_iff r z).mp hz
    exact ⟨(TrominoAssignment.mem_boxCellList_iff r xy).mp hxy,
      by simp only [LeanWang.InBox] at hz ⊢; omega⟩
  · rintro ⟨hxy, hz⟩
    exact ⟨c.1, (TrominoAssignment.mem_boxCellList_iff r c.1).mpr hxy,
      (c.2, 0), (TrominoAssignment.mem_boxCellList_iff r (c.2, 0)).mpr hz, rfl⟩

noncomputable def pool (input : Input) (radius : Nat) : List (VoxelPlacement Bool) :=
  (boxVoxelList radius).flatMap (candidates input)

open PlaneTilingSearch (subsets filter_mem_subsets)

def Valid (input : Input) (region : Set Voxel) (radius : Nat)
    (selected : List (VoxelPlacement Bool)) : Prop :=
  ∀ c ∈ boxVoxelList radius,
    if c ∈ region then
      ∃ p ∈ selected, c ∈ p.cells (tiles input) ∧
        ∀ q ∈ selected, c ∈ q.cells (tiles input) → q = p
    else ∀ p ∈ selected, c ∉ p.cells (tiles input)

def FiniteSearch (input : Input) (region : Set Voxel) (radius : Nat) : Prop :=
  ∃ selected ∈ subsets (pool input radius), Valid input region radius selected

theorem finiteSearch_of_tileable (input : Input) (region : Set Voxel)
    (tiled : VoxelTileable (tiles input) region) (radius : Nat) : FiniteSearch input region radius := by
  classical
  obtain ⟨ps, ht⟩ := tiled
  refine ⟨(pool input radius).filter (fun p => decide (p ∈ ps)), filter_mem_subsets _ _, ?_⟩
  intro c hc
  by_cases inside : c ∈ region
  · simp only [inside, ↓reduceIte]
    obtain ⟨p, hp, unique⟩ := ht.uniqueCover c inside
    refine ⟨p, ?_, hp.2, ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq]
      refine ⟨List.mem_flatMap.mpr ⟨c, hc, (mem_candidates input c p).mpr hp.2⟩, hp.1⟩
    · intro q hq covers
      exact unique q ⟨by simpa using (List.mem_filter.mp hq).2, covers⟩
  · simp only [inside, ↓reduceIte]
    intro p hp cover
    exact inside (ht.tilesInside p (by simpa using (List.mem_filter.mp hp).2) c cover)

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot _
local instance : CompactSpace Bool := Finite.compactSpace

attribute [local instance] Classical.propDecidable

private def patch (input : Input) (region : Set Voxel) (radius : Nat) :
    Set (VoxelTilingSelection.Selection Bool) :=
  {f | ∀ c, InBox radius c →
    VoxelTilingSelection.count (tiles input) c f = if c ∈ region then 1 else 0}

private theorem patch_closed (input : Input) (region : Set Voxel) (radius : Nat) :
    IsClosed (patch input region radius) := by
  unfold patch
  convert isClosed_iInter (fun c => isClosed_iInter (fun (_ : InBox radius c) =>
    VoxelTilingSelection.isClosed_count (tiles input) c (if c ∈ region then 1 else 0))) using 1
  ext f
  simp

theorem tileable_of_all_finiteSearch (input : Input) (region : Set Voxel)
    (finite : ∀ r, FiniteSearch input region r) : VoxelTileable (tiles input) region := by
  classical
  have nonempty (r : Nat) : (patch input region r).Nonempty := by
    obtain ⟨selected, _, valid⟩ := finite r
    let f : VoxelTilingSelection.Selection Bool := fun p => decide (p ∈ selected)
    refine ⟨f, ?_⟩
    intro c hc
    have hv := valid c ((mem_boxVoxelList r c).mpr hc)
    by_cases inside : c ∈ region
    · simp only [inside, ↓reduceIte] at hv ⊢
      rw [VoxelTilingSelection.count_eq_one_iff]
      obtain ⟨p, hp, covers, unique⟩ := hv
      refine ⟨p, ⟨by simpa [VoxelTilingSelection.placements, f] using hp, covers⟩, ?_⟩
      intro q hq
      exact unique q (by simpa [VoxelTilingSelection.placements, f] using hq.1) hq.2
    · simp only [inside, ↓reduceIte] at hv ⊢
      rw [VoxelTilingSelection.count_eq_zero_iff]
      intro p hp
      exact hv p (by simpa [VoxelTilingSelection.placements, f] using hp)
  have decreasing (r : Nat) : patch input region (r + 1) ⊆ patch input region r := by
    intro f h c hc
    exact h c ⟨LeanWang.inBox_mono (by omega) hc.1, LeanWang.inBox_mono (by omega) hc.2⟩
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (patch input region) decreasing nonempty (patch_closed input region 0).isCompact
      (patch_closed input region)
  refine ⟨VoxelTilingSelection.placements f, (VoxelTilingSelection.isTiling_iff_count _ _ _).mpr ?_⟩
  intro c
  have all : ∀ r, f ∈ patch input region r := by simpa using hf
  exact all (max (max c.1.1.natAbs c.1.2.natAbs) c.2.natAbs) c
    ⟨LeanWang.inBox_of_natAbs_le (by omega) (by omega),
      LeanWang.inBox_of_natAbs_le (by omega) (by simp)⟩

theorem tileable_iff (input : Input) (region : Set Voxel) :
    VoxelTileable (tiles input) region ↔ ∀ r, FiniteSearch input region r :=
  ⟨finiteSearch_of_tileable input region, tileable_of_all_finiteSearch input region⟩

end LeanTrominoes.VoxelTilingSearch
