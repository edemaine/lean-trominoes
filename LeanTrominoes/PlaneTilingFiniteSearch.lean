/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingPrescribedCompactness
import LeanTrominoes.ComputableSearch
import LeanTrominoes.TilingPair

/-! # Finite obstructions for plane tiling by two arbitrary finite shapes -/

namespace LeanTrominoes.PlaneTilingSearch

abbrev Input := List Cell × List Cell

def tileList (input : Input) (kind : Bool) : List Cell := if kind then input.2 else input.1

def tiles (input : Input) : Bool → Polyomino := fun kind => (tileList input kind).toFinset

def candidates (input : Input) (c : Cell) : List (Placement Bool) :=
  [false, true].flatMap fun kind => TrominoAssignment.squareSymmetryList.flatMap fun symmetry =>
    (tileList input kind).map fun q => ⟨kind, symmetry, Cell.sub c (symmetry.act q)⟩

theorem mem_candidates (input : Input) (c : Cell) (p : Placement Bool) :
    p ∈ candidates input c ↔ c ∈ p.cells (tiles input) := by
  simp only [candidates, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨k, _, s, _, q, hq, rfl⟩
    rw [Placement.mem_cells_iff]
    refine ⟨q, List.mem_toFinset.mpr hq, ?_⟩
    apply Prod.ext <;> dsimp [Cell.add, Cell.sub] <;> omega
  · rw [Placement.mem_cells_iff]
    rintro ⟨q, hq, eq⟩
    refine ⟨p.kind, by cases p.kind <;> simp,
      p.symmetry, ?_, q, List.mem_toFinset.mp hq, ?_⟩
    · cases p.symmetry <;> simp [TrominoAssignment.squareSymmetryList]
    · apply Placement.ext
      · rfl
      · rfl
      · have hx := congrArg Prod.fst eq
        have hy := congrArg Prod.snd eq
        apply Prod.ext <;> dsimp [Cell.add, Cell.sub] at * <;> omega

def pool (input : Input) (radius : Nat) : List (Placement Bool) :=
  (TrominoAssignment.boxCellList radius).flatMap (candidates input)

def subsets {α : Type*} : List α → List (List α)
  | [] => [[]]
  | x :: xs => subsets xs ++ (subsets xs).map (x :: ·)

theorem filter_mem_subsets {α : Type*} (xs : List α) (p : α → Bool) :
    xs.filter p ∈ subsets xs := by
  induction xs with
  | nil => simp [subsets]
  | cons x xs ih =>
    cases h : p x <;> simp [subsets, h, ih]

def Valid (input : Input) (radius : Nat) (selected : List (Placement Bool)) : Prop :=
  ∀ c ∈ TrominoAssignment.boxCellList radius,
    ∃ p ∈ selected, c ∈ p.cells (tiles input) ∧
      ∀ q ∈ selected, c ∈ q.cells (tiles input) → q = p

instance (input : Input) (radius : Nat) (selected : List (Placement Bool)) :
    Decidable (Valid input radius selected) := by
  unfold Valid
  infer_instance

def FiniteSearch (input : Input) (radius : Nat) : Prop :=
  ∃ selected ∈ subsets (pool input radius), Valid input radius selected

instance (input : Input) (radius : Nat) : Decidable (FiniteSearch input radius) := by
  unfold FiniteSearch
  infer_instance

theorem finiteSearch_of_tileable (input : Input)
    (tiled : Tileable (tiles input) Set.univ) (radius : Nat) : FiniteSearch input radius := by
  classical
  obtain ⟨ps, ht⟩ := tiled
  refine ⟨(pool input radius).filter (fun p => decide (p ∈ ps)), filter_mem_subsets _ _, ?_⟩
  intro c hc
  obtain ⟨p, hp, unique⟩ := ht.uniqueCover c (Set.mem_univ _)
  refine ⟨p, ?_, hp.2, ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq]
    refine ⟨List.mem_flatMap.mpr ⟨c, hc, (mem_candidates input c p).mpr hp.2⟩, hp.1⟩
  · intro q hq covers
    exact unique q ⟨by simpa using (List.mem_filter.mp hq).2, covers⟩

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot _
local instance : CompactSpace Bool := Finite.compactSpace

private def patch (input : Input) (radius : Nat) : Set (TilingSelection.Selection Bool) :=
  {f | ∀ c, LeanWang.InBox radius c → TilingSelection.count (tiles input) c f = 1}

private theorem patch_closed (input : Input) (radius : Nat) : IsClosed (patch input radius) := by
  unfold patch
  convert isClosed_iInter (fun c => isClosed_iInter (fun (_ : LeanWang.InBox radius c) =>
    TilingSelection.isClosed_count (tiles input) c)) using 1
  ext f
  simp

theorem tileable_of_all_finiteSearch (input : Input) (finite : ∀ r, FiniteSearch input r) :
    Tileable (tiles input) Set.univ := by
  classical
  have nonempty (r : Nat) : (patch input r).Nonempty := by
    obtain ⟨selected, _, valid⟩ := finite r
    let f : TilingSelection.Selection Bool := fun p => decide (p ∈ selected)
    refine ⟨f, ?_⟩
    intro c hc
    rw [TilingSelection.count_eq_one_iff]
    obtain ⟨p, hp, covers, unique⟩ := valid c ((TrominoAssignment.mem_boxCellList_iff r c).mpr hc)
    refine ⟨p, ⟨by simpa [TilingSelection.placements, f] using hp, covers⟩, ?_⟩
    intro q hq
    exact unique q (by simpa [TilingSelection.placements, f] using hq.1) hq.2
  have decreasing (r : Nat) : patch input (r + 1) ⊆ patch input r := by
    intro f h c hc
    exact h c (LeanWang.inBox_mono (by omega) hc)
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (patch input) decreasing nonempty (patch_closed input 0).isCompact (patch_closed input)
  refine ⟨TilingSelection.placements f, (TilingSelection.isTiling_iff_count _ _).mpr ?_⟩
  intro c
  have all : ∀ r, f ∈ patch input r := by simpa using hf
  exact all (max c.1.natAbs c.2.natAbs) c
    (LeanWang.inBox_of_natAbs_le (Nat.le_max_left _ _) (Nat.le_max_right _ _))

theorem tileable_iff (input : Input) :
    Tileable (tiles input) Set.univ ↔ ∀ r, FiniteSearch input r :=
  ⟨finiteSearch_of_tileable input, tileable_of_all_finiteSearch input⟩

end LeanTrominoes.PlaneTilingSearch
