/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteICompletionRays
import LeanTrominoes.FiniteCompletionBox

/-! # Deciding completion of a finite straight-tromino preplacement

A finite box-cover certificate suffices even when some selected tiles cross
its boundary. The algorithm searches a finite candidate set, and the soundness
proof constructs a tiling of the whole infinite exterior.
-/
namespace LeanTrominoes.Tromino.FiniteI
open FiniteWitness

theorem completion_of_witness {r : Nat} {prefill tiles : Finset (Finset Cell)}
    (witness : Valid Tromino.I (box r) prefill tiles) :
    Tromino.I.Completable Set.univ (prefill : Set (Finset Cell)) := by
  have boundary : Boundary r tiles := by
    constructor
    · intro f hf; exact ((mem_candidates _ _ _).mp (witness.1 hf)).1
    · intro f hf
      obtain ⟨c,hc,hcf⟩ := ((mem_candidates _ _ _).mp (witness.1 hf)).2
      exact ⟨c,hcf,(mem_box r c).mp hc⟩
    · intro c hc
      exact (mem_cellsOf _ _).mpr (witness.2.2.2 c ((mem_box r c).mpr hc))
  have occupied_eq : occupied (tiles : Set (Finset Cell))=(cellsOf tiles : Set Cell) := by
    ext c; exact (mem_cellsOf tiles c).symm
  have tiled : Tromino.I.Tileable (Set.univ \ occupied (tiles : Set (Finset Cell))) := by
    rw [occupied_eq]; exact boundary.exterior_tileable
  obtain ⟨completed,h,retained⟩ := (Tromino.I.completable_iff _ _).mpr ⟨witness.partial,tiled⟩
  exact ⟨completed,h,fun f hf => retained (witness.2.1 hf)⟩

/-- A closed executable decision, including bounding-box construction. -/
def decideCompletion (prefill : Finset (Finset Cell)) : Bool :=
  check Tromino.I (box (radius prefill)) prefill

theorem decideCompletion_correct (prefill : Finset (Finset Cell)) :
    decideCompletion prefill=true ↔ Tromino.I.Completable Set.univ (prefill : Set (Finset Cell)) := by
  rw [decideCompletion,check_correct]
  constructor
  · rintro ⟨tiles,h⟩; exact completion_of_witness h
  · intro completion
    exact of_completion Tromino.I _ prefill (completion_meets_box Tromino.I prefill completion) completion

/-- The finite witnesses have at most as many tiles as cells in the box. -/
theorem completion_iff_bounded_witness (prefill : Finset (Finset Cell)) :
    Tromino.I.Completable Set.univ (prefill : Set (Finset Cell)) ↔
    ∃ tiles, Valid Tromino.I (box (radius prefill)) prefill tiles ∧
      tiles.card≤(box (radius prefill)).card := by
  constructor
  · intro completion
    obtain ⟨tiles,h⟩ := of_completion Tromino.I _ prefill
      (completion_meets_box Tromino.I prefill completion) completion
    exact ⟨tiles,h,h.card_le⟩
  · rintro ⟨tiles,h,_⟩; exact completion_of_witness h

end LeanTrominoes.Tromino.FiniteI
