/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Periodic.PlaneTilingSearchComputability

/-! # Finite-seed plane completion by two polyominoes

The tile shapes and the finite list of prescribed placements are explicit
input. A finite search keeps every prescribed placement, including placements
outside the current box. Compactness then produces one plane tiling retaining
the entire seed. Overlapping prescribed placements fail at a sufficiently
large box; no validity promise is required of the input.
-/

namespace LeanTrominoes.FinitePolyominoCompletion

abbrev Input := PlaneTilingSearch.Input × List (Placement Bool)

/-- A plane tiling retaining every prescribed placement. -/
def Completable (input : Input) : Prop :=
  ∃ ps, IsTiling (PlaneTilingSearch.tiles input.1) Set.univ ps ∧
    ∀ p ∈ input.2, p ∈ ps

/-- Candidate placements covering the box, together with the entire seed. -/
def pool (input : Input) (radius : Nat) : List (Placement Bool) :=
  PlaneTilingSearch.pool input.1 radius ++ input.2

def Valid (input : Input) (radius : Nat) (selected : List (Placement Bool)) : Prop :=
  PlaneTilingSearch.Valid input.1 radius selected ∧ input.2 ⊆ selected

instance (input : Input) (radius : Nat) (selected : List (Placement Bool)) :
    Decidable (Valid input radius selected) := by
  unfold Valid
  infer_instance

def FiniteSearch (input : Input) (radius : Nat) : Prop :=
  ∃ selected ∈ PlaneTilingSearch.subsets (pool input radius),
    Valid input radius selected

instance (input : Input) (radius : Nat) : Decidable (FiniteSearch input radius) := by
  unfold FiniteSearch
  infer_instance

theorem finiteSearch_of_completable (input : Input)
    (completed : Completable input) (radius : Nat) : FiniteSearch input radius := by
  classical
  obtain ⟨ps, ht, retained⟩ := completed
  refine ⟨(pool input radius).filter (fun p => decide (p ∈ ps)),
    PlaneTilingSearch.filter_mem_subsets _ _, ?_, ?_⟩
  · intro c hc
    obtain ⟨p, hp, unique⟩ := ht.uniqueCover c (Set.mem_univ _)
    refine ⟨p, ?_, hp.2, ?_⟩
    · apply List.mem_filter.mpr
      refine ⟨List.mem_append_left _ ?_, by simpa using hp.1⟩
      exact List.mem_flatMap.mpr
        ⟨c, hc, (PlaneTilingSearch.mem_candidates input.1 c p).mpr hp.2⟩
    · intro q hq covers
      exact unique q ⟨by simpa using (List.mem_filter.mp hq).2, covers⟩
  · intro p hp
    exact List.mem_filter.mpr
      ⟨List.mem_append_right _ hp, by simpa using retained p hp⟩

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot _
local instance : CompactSpace Bool := Finite.compactSpace

private def patch (input : Input) (radius : Nat) : Set (TilingSelection.Selection Bool) :=
  {f | (∀ c, LeanWang.InBox radius c →
      TilingSelection.count (PlaneTilingSearch.tiles input.1) c f = 1) ∧
    ∀ p ∈ input.2, f p = true}

private theorem patch_closed (input : Input) (radius : Nat) :
    IsClosed (patch input radius) := by
  have counts : IsClosed {f : TilingSelection.Selection Bool |
      ∀ c, LeanWang.InBox radius c →
        TilingSelection.count (PlaneTilingSearch.tiles input.1) c f = 1} := by
    convert isClosed_iInter (fun c => isClosed_iInter
      (fun (_ : LeanWang.InBox radius c) =>
        TilingSelection.isClosed_count (PlaneTilingSearch.tiles input.1) c)) using 1
    ext f
    simp
  have seed : IsClosed {f : TilingSelection.Selection Bool |
      ∀ p ∈ input.2, f p = true} := by
    convert isClosed_iInter (fun p => isClosed_iInter (fun (_ : p ∈ input.2) =>
      (isClosed_singleton : IsClosed ({true} : Set Bool)).preimage
        (continuous_apply p))) using 1
    ext f
    simp
  exact counts.inter seed

theorem completable_of_all_finiteSearch (input : Input)
    (finite : ∀ r, FiniteSearch input r) : Completable input := by
  classical
  have nonempty (r : Nat) : (patch input r).Nonempty := by
    obtain ⟨selected, _, valid, retained⟩ := finite r
    let f : TilingSelection.Selection Bool := fun p => decide (p ∈ selected)
    refine ⟨f, ?_, ?_⟩
    · intro c hc
      rw [TilingSelection.count_eq_one_iff]
      obtain ⟨p, hp, covers, unique⟩ :=
        valid c ((TrominoAssignment.mem_boxCellList_iff r c).mpr hc)
      refine ⟨p, ⟨by simpa [TilingSelection.placements, f] using hp, covers⟩, ?_⟩
      intro q hq
      exact unique q (by simpa [TilingSelection.placements, f] using hq.1) hq.2
    · intro p hp
      simpa [f] using retained hp
  have decreasing (r : Nat) : patch input (r + 1) ⊆ patch input r := by
    intro f h
    exact ⟨fun c hc => h.1 c (LeanWang.inBox_mono (by omega) hc), h.2⟩
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (patch input) decreasing nonempty (patch_closed input 0).isCompact (patch_closed input)
  have all : ∀ r, f ∈ patch input r := by simpa using hf
  refine ⟨TilingSelection.placements f,
    (TilingSelection.isTiling_iff_count _ _).mpr ?_, ?_⟩
  · intro c
    exact (all (max c.1.natAbs c.2.natAbs)).1 c
      (LeanWang.inBox_of_natAbs_le (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  · exact (all 0).2

/-- Completion has a finite obstruction exactly when it fails. -/
theorem completable_iff (input : Input) :
    Completable input ↔ ∀ r, FiniteSearch input r :=
  ⟨finiteSearch_of_completable input, completable_of_all_finiteSearch input⟩

/-- Distinct prescribed placements in a completable seed are disjoint. -/
theorem seed_cells_disjoint {input : Input} (completed : Completable input)
    {p q : Placement Bool} (hp : p ∈ input.2) (hq : q ∈ input.2) (different : p ≠ q) :
    Disjoint (p.cells (PlaneTilingSearch.tiles input.1))
      (q.cells (PlaneTilingSearch.tiles input.1)) := by
  obtain ⟨ps, tiling, retained⟩ := completed
  exact tiling.disjoint_cells (retained p hp) (retained q hq) different

/-- Removing prescriptions preserves completion, with the shapes unchanged. -/
theorem completable_mono_seed (shapes : PlaneTilingSearch.Input)
    {smaller larger : List (Placement Bool)} (subset : smaller ⊆ larger)
    (completed : Completable (shapes, larger)) : Completable (shapes, smaller) := by
  obtain ⟨ps, tiling, retained⟩ := completed
  exact ⟨ps, tiling, fun p hp => retained p (subset hp)⟩

end LeanTrominoes.FinitePolyominoCompletion
