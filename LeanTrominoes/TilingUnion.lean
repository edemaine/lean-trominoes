/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling

/-! # Combining and restricting tilings of disjoint regions -/

namespace LeanTrominoes

/-- Exact tilings of disjoint regions combine. -/
theorem Tileable.union {ι : Type*} (tiles : ι → Polyomino) (s t : Set Cell)
    (disjoint : Disjoint s t) (hs : Tileable tiles s) (ht : Tileable tiles t) :
    Tileable tiles (s ∪ t) := by
  obtain ⟨ps, st⟩ := hs
  obtain ⟨pt, tt⟩ := ht
  refine ⟨ps ∪ pt, ?_, ?_⟩
  · rintro p (hp | hp) c hc
    · exact Or.inl (st.tilesInside p hp c hc)
    · exact Or.inr (tt.tilesInside p hp c hc)
  · rintro c (hc | hc)
    · obtain ⟨p, ⟨hp, hpc⟩, unique⟩ := st.uniqueCover c hc
      refine ⟨p, ⟨Or.inl hp, hpc⟩, ?_⟩
      rintro q ⟨hq | hq, hqc⟩
      · exact unique q ⟨hq, hqc⟩
      · exact False.elim (Set.disjoint_left.mp disjoint hc (tt.tilesInside q hq c hqc))
    · obtain ⟨p, ⟨hp, hpc⟩, unique⟩ := tt.uniqueCover c hc
      refine ⟨p, ⟨Or.inr hp, hpc⟩, ?_⟩
      rintro q ⟨hq | hq, hqc⟩
      · exact False.elim (Set.disjoint_left.mp disjoint (st.tilesInside q hq c hqc) hc)
      · exact unique q ⟨hq, hqc⟩

/-- If no placed tile can meet both regions, a tiling of their union
restricts to a tiling of either region. -/
theorem Tileable.restrict_left {ι : Type*} (tiles : ι → Polyomino) (s t : Set Cell)
    (disjoint : Disjoint s t)
    (classify : ∀ p : Placement ι, (∀ c ∈ p.cells tiles, c ∈ s ∪ t) →
      (∀ c ∈ p.cells tiles, c ∈ s) ∨ (∀ c ∈ p.cells tiles, c ∈ t))
    (tiled : Tileable tiles (s ∪ t)) : Tileable tiles s := by
  obtain ⟨ps, tiling⟩ := tiled
  refine ⟨{p | p ∈ ps ∧ ∀ c ∈ p.cells tiles, c ∈ s}, ?_, ?_⟩
  · exact fun p hp c hc => hp.2 c hc
  · intro c hc
    obtain ⟨p, ⟨hp, hpc⟩, unique⟩ := tiling.uniqueCover c (Or.inl hc)
    have inside : ∀ c ∈ p.cells tiles, c ∈ s := by
      rcases classify p (tiling.tilesInside p hp) with hs | ht
      · exact hs
      · exact False.elim (Set.disjoint_left.mp disjoint hc (ht c hpc))
    refine ⟨p, ⟨⟨hp, inside⟩, hpc⟩, ?_⟩
    rintro q ⟨hq, hqc⟩
    exact unique q ⟨hq.1, hqc⟩

end LeanTrominoes
