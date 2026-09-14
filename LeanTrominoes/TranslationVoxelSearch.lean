/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolycubes
import LeanTrominoes.PolycubeSearchComputability

/-! # Finite obstructions with restricted polycube orientations -/

namespace LeanTrominoes.TranslationVoxelSearch
open VoxelTilingSearch
open PlaneTilingSearch (subsets filter_mem_subsets subsets_primrec)
open ThreeTranslationPolycubes (Allowed)

attribute [local instance] Classical.propDecidable

def FiniteSearch (input : Input) (region : Set Voxel) (radius : Nat) : Prop :=
  ∃ selected ∈ subsets (pool input radius), Valid input region radius selected ∧ ∀ p ∈ selected, Allowed p

theorem finiteSearch_of_tileable (input : Input) (region : Set Voxel)
    (tiled : VoxelTileableWith (tiles input) region Allowed) (radius : Nat) : FiniteSearch input region radius := by
  classical
  obtain ⟨ps, ht, legal⟩ := tiled
  refine ⟨(pool input radius).filter (fun p => decide (p ∈ ps)), filter_mem_subsets _ _, ?_, ?_⟩
  · intro c hc
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
  · intro p hp
    exact legal p (by simpa using (List.mem_filter.mp hp).2)

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot _
local instance : CompactSpace Bool := Finite.compactSpace

attribute [local instance] Classical.propDecidable

private def patch (input : Input) (region : Set Voxel) (radius : Nat) :
    Set (VoxelTilingSelection.Selection Bool) :=
  {f | (∀ c, InBox radius c →
    VoxelTilingSelection.count (tiles input) c f = if c ∈ region then 1 else 0) ∧
    ∀ p, ¬ Allowed p → f p = false}

private theorem patch_closed (input : Input) (region : Set Voxel) (radius : Nat) :
    IsClosed (patch input region radius) := by
  have counts : IsClosed {f | ∀ c, InBox radius c →
      VoxelTilingSelection.count (tiles input) c f = if c ∈ region then 1 else 0} := by
    convert isClosed_iInter (fun c => isClosed_iInter (fun (_ : InBox radius c) =>
      VoxelTilingSelection.isClosed_count (tiles input) c (if c ∈ region then 1 else 0))) using 1
    ext f
    simp
  have legality : IsClosed {f : VoxelTilingSelection.Selection Bool | ∀ p, ¬ Allowed p → f p = false} := by
    convert isClosed_iInter (fun p => isClosed_iInter (fun (_ : ¬ Allowed p) =>
      (isClosed_discrete ({false} : Set Bool)).preimage (continuous_apply p))) using 1
    ext f
    simp
  exact counts.inter legality

theorem tileable_of_all_finiteSearch (input : Input) (region : Set Voxel)
    (finite : ∀ r, FiniteSearch input region r) : VoxelTileableWith (tiles input) region Allowed := by
  classical
  have nonempty (r : Nat) : (patch input region r).Nonempty := by
    obtain ⟨selected, _, valid, legal⟩ := finite r
    let f : VoxelTilingSelection.Selection Bool := fun p => decide (p ∈ selected)
    refine ⟨f, ?_, ?_⟩
    · intro c hc
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
    · intro p forbidden
      have outside : p ∉ selected := fun hp => forbidden (legal p hp)
      simp [f, outside]
  have decreasing (r : Nat) : patch input region (r + 1) ⊆ patch input region r := by
    intro f h
    exact ⟨fun c hc => h.1 c ⟨LeanWang.inBox_mono (by omega) hc.1, LeanWang.inBox_mono (by omega) hc.2⟩,h.2⟩
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (patch input region) decreasing nonempty (patch_closed input region 0).isCompact
      (patch_closed input region)
  have all : ∀ r, f ∈ patch input region r := by simpa using hf
  refine ⟨VoxelTilingSelection.placements f, (VoxelTilingSelection.isTiling_iff_count _ _ _).mpr ?_, ?_⟩
  · intro c
    exact (all (max (max c.1.1.natAbs c.1.2.natAbs) c.2.natAbs)).1 c
      ⟨LeanWang.inBox_of_natAbs_le (by omega) (by omega),
        LeanWang.inBox_of_natAbs_le (by omega) (by simp)⟩
  · intro p hp
    by_contra forbidden
    have zero := (all 0).2 p forbidden
    change f p = true at hp
    rw [zero] at hp
    contradiction

theorem tileable_iff (input : Input) (region : Set Voxel) :
    VoxelTileableWith (tiles input) region Allowed ↔ ∀ r, FiniteSearch input region r :=
  ⟨finiteSearch_of_tileable input region, tileable_of_all_finiteSearch input region⟩

theorem allowed_primrec : PrimrecPred Allowed := by
  have data : Primrec (fun p : VoxelPlacement Bool => symmetryEquiv p.symmetry) :=
    symmetry_data_primrec.comp symmetry_primrec
  have axis : Primrec (fun p : VoxelPlacement Bool => p.symmetry.axis) :=
    Primrec.snd.comp (Primrec.snd.comp data)
  have flip : Primrec (fun p : VoxelPlacement Bool => p.symmetry.flip) :=
    Primrec.fst.comp (Primrec.snd.comp data)
  have planar : Primrec (fun p : VoxelPlacement Bool => p.symmetry.planar) :=
    Primrec.fst.comp data
  exact ((Primrec.eq.comp axis (Primrec.const 0)).and
    ((Primrec.eq.comp flip (Primrec.const false)).and
      ((Primrec.eq.comp kind_primrec (Primrec.const true)).not.or
        (Primrec.eq.comp planar (Primrec.const SquareSymmetry.identity))))).of_eq
    (fun _ => by simp [Allowed,imp_iff_not_or])

theorem finiteSearch_primrec (region : Set Voxel)
    (regionPR : PrimrecPred (fun c => c ∈ region)) :
    PrimrecRel (fun input radius => FiniteSearch input region radius) := by
  have legal : PrimrecPred (fun ps : List (VoxelPlacement Bool) => ∀ p ∈ ps, Allowed p) :=
    allowed_primrec.forall_mem_list
  have selected : PrimrecRel (fun (ps : List (VoxelPlacement Bool)) (a : Input × Nat) =>
      Valid a.1 region a.2 ps ∧ ∀ p ∈ ps, Allowed p) :=
    ((valid_primrec region regionPR).comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst))).and (legal.comp Primrec.fst)
  exact selected.exists_mem_list.comp (subsets_primrec.comp pool_primrec) Primrec.id

end LeanTrominoes.TranslationVoxelSearch
