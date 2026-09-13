/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling
import LeanWang.Compactness
import Mathlib.Data.Finset.Union

/-! # Compactness of lattice-region tilings with prescribed placements

A placement is either selected or absent. For a finite family of finite
prototiles, only finitely many placements can cover a given cell. Exact
coverage is therefore a closed condition in the compact space of selections.
-/

namespace LeanTrominoes.RegionTilingSelection

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Select or omit every possible placement. -/
abbrev Selection (ι : Type*) := Placement ι → Bool

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot _
local instance : CompactSpace Bool := Finite.compactSpace

/-- All placements that can cover a given cell. -/
def candidates (tiles : ι → Polyomino) (c : Cell) : Finset (Placement ι) :=
  Finset.univ.biUnion fun k => Finset.univ.biUnion fun s : SquareSymmetry =>
    (tiles k).image fun q => ⟨k, s, Cell.sub c (s.act q)⟩

theorem mem_candidates (tiles : ι → Polyomino) (c : Cell) (p : Placement ι) :
    p ∈ candidates tiles c ↔ c ∈ p.cells tiles := by
  simp only [candidates, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Placement.mem_cells_iff]
  constructor
  · rintro ⟨k, s, q, hq, rfl⟩
    refine ⟨q,hq,?_⟩
    apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
  · rintro ⟨q, hq, he⟩
    refine ⟨p.kind, p.symmetry, q, hq, ?_⟩
    apply Placement.ext
    · rfl
    · rfl
    · simp only [Cell.add, Prod.ext_iff] at he
      simp only [Cell.sub, Prod.ext_iff]
      exact ⟨by omega, by omega⟩

/-- Selected placements. -/
def placements (f : Selection ι) : Set (Placement ι) := {p | f p = true}

def count (tiles : ι → Polyomino) (c : Cell) (f : Selection ι) : Nat :=
  ((candidates tiles c).filter fun p => f p = true).card

theorem count_eq_one_iff (tiles : ι → Polyomino) (c : Cell) (f : Selection ι) :
    count tiles c f = 1 ↔ ∃! p, p ∈ placements f ∧ c ∈ p.cells tiles := by
  rw [count, Finset.card_eq_one]
  constructor
  · rintro ⟨p, eq⟩
    have hp : p ∈ (candidates tiles c).filter (fun p => f p = true) := by
      rw [eq]
      exact Finset.mem_singleton_self _
    obtain ⟨hc, hf⟩ := Finset.mem_filter.mp hp
    refine ⟨p, ⟨hf, (mem_candidates tiles c p).mp hc⟩, ?_⟩
    intro q hq
    have member : q ∈ (candidates tiles c).filter (fun p => f p = true) :=
      Finset.mem_filter.mpr ⟨(mem_candidates tiles c q).mpr hq.2, hq.1⟩
    rw [eq] at member
    exact Finset.mem_singleton.mp member
  · rintro ⟨p, hp, unique⟩
    refine ⟨p, Finset.ext fun q => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_singleton, mem_candidates]
    constructor
    · intro hq
      exact unique q ⟨hq.2, hq.1⟩
    · rintro rfl
      exact ⟨hp.2, hp.1⟩

theorem count_eq_zero_iff (tiles : ι → Polyomino) (c : Cell) (f : Selection ι) :
    count tiles c f = 0 ↔ ∀ p ∈ placements f, c ∉ p.cells tiles := by
  simp only [count, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem,
    Finset.mem_filter, mem_candidates, placements, Set.mem_setOf_eq]
  tauto

theorem isTiling_iff_count (tiles : ι → Polyomino) (region : Set Cell) (f : Selection ι) :
    IsTiling tiles region (placements f) ↔
      ∀ c, count tiles c f = if c ∈ region then 1 else 0 := by
  constructor
  · intro h c
    by_cases hc : c ∈ region
    · simpa only [hc, ↓reduceIte] using
        (count_eq_one_iff tiles c f).mpr (h.uniqueCover c hc)
    · have hz : count tiles c f = 0 := (count_eq_zero_iff tiles c f).mpr
        (fun p hp hpc => hc (h.tilesInside p hp c hpc))
      simpa only [hc, ↓reduceIte] using hz
  · intro h
    constructor
    · intro p hp c hc
      by_contra outside
      have hz : count tiles c f = 0 := by simpa only [outside, ↓reduceIte] using h c
      exact (count_eq_zero_iff tiles c f).mp hz p hp hc
    · intro c hc
      apply (count_eq_one_iff tiles c f).mp
      simpa only [hc, ↓reduceIte] using h c

theorem isClosed_count (tiles : ι → Polyomino) (c : Cell) (value : Nat) :
    IsClosed {f : Selection ι | count tiles c f = value} := by
  let observe : Selection ι → (↑(candidates tiles c) → Bool) := fun f p => f p.val
  have continuous_observe : Continuous observe :=
    continuous_pi fun p => continuous_apply p.val
  let finiteCount (states : ↑(candidates tiles c) → Bool) : Nat :=
    ((candidates tiles c).attach.filter fun p => states p = true).card
  have closed : IsClosed {states | finiteCount states = value} := isClosed_discrete _
  have same (f : Selection ι) : finiteCount (observe f) = count tiles c f := by
    have eq := congrArg Finset.card (Finset.filter_attach (fun p => f p = true) (candidates tiles c))
    simpa only [finiteCount, observe, count, Finset.card_map, Finset.card_attach] using eq
  convert closed.preimage continuous_observe using 1
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_preimage, same]

theorem isClosed_tilings (tiles : ι → Polyomino) (region : Set Cell) :
    IsClosed {f : Selection ι | IsTiling tiles region (placements f)} := by
  convert isClosed_iInter (fun c => isClosed_count tiles c (if c ∈ region then 1 else 0)) using 1
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_iInter, isTiling_iff_count]

private def cylinder (tiles : ι → Polyomino) (region : Set Cell) (required : Set (Placement ι)) :
    Set (Selection ι) :=
  {f | IsTiling tiles region (placements f) ∧ required ⊆ placements f}

private theorem isClosed_cylinder (tiles : ι → Polyomino) (region : Set Cell) (required : Set (Placement ι)) :
    IsClosed (cylinder tiles region required) := by
  unfold cylinder
  rw [Set.setOf_and]
  apply (isClosed_tilings tiles region).inter
  convert isClosed_iInter (fun p => isClosed_iInter (fun (_ : p ∈ required) =>
    (isClosed_discrete ({true} : Set Bool)).preimage (continuous_apply p))) using 1
  ext f
  simp [placements, Set.subset_def]

/-- Increasing prescriptions can be imposed simultaneously if each stage is
realized by some tiling of the same region. -/
theorem exists_tiling_of_prescriptions (tiles : ι → Polyomino) (region : Set Cell)
    (required : Nat → Set (Placement ι))
    (increasing : ∀ r, required r ⊆ required (r + 1))
    (realized : ∀ r, ∃ ps, IsTiling tiles region ps ∧ required r ⊆ ps) :
    ∃ ps, IsTiling tiles region ps ∧ ∀ r, required r ⊆ ps := by
  classical
  have nonempty (r : Nat) : (cylinder tiles region (required r)).Nonempty := by
    obtain ⟨ps, ht, hr⟩ := realized r
    let f : Selection ι := fun p => decide (p ∈ ps)
    have eq : placements f = ps := by ext p; simp [placements, f]
    refine ⟨f, ?_⟩
    change IsTiling tiles region (placements f) ∧ required r ⊆ placements f
    rw [eq]
    exact ⟨ht, hr⟩
  have decreasing (r : Nat) : cylinder tiles region (required (r + 1)) ⊆ cylinder tiles region (required r) :=
    fun _ h => ⟨h.1, (increasing r).trans h.2⟩
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun r => cylinder tiles region (required r)) decreasing nonempty
    (isClosed_cylinder tiles region (required 0)).isCompact (fun r => isClosed_cylinder tiles region (required r))
  have all : ∀ r, f ∈ cylinder tiles region (required r) := by simpa using hf
  exact ⟨placements f, (all 0).1, fun r => (all r).2⟩

end LeanTrominoes.RegionTilingSelection
