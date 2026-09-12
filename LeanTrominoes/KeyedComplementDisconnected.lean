/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementRefinedExclusion
import LeanTrominoes.PolyominoSeparation

/-! # A finite witness for disconnectedness of the keyed complement -/

namespace LeanTrominoes.KeyedPeriodicComplement

/-- The eight side neighbors of the central 2-by-2 block of a 4-by-4 square. -/
def isolationRing : Polyomino :=
  {(1, 0), (2, 0), (0, 1), (0, 2), (3, 1), (3, 2), (1, 3), (2, 3)}

/-- Refining a 2-by-2 source block creates the isolating ring. -/
theorem isolationRing_subset_refinement :
    isolationRing ⊆ PlusRefinement.polyomino PlusRefinement.unitSquare := by decide

/-- A source 2-by-2 block produces the ring in the refined region. -/
theorem ring_inside_refined_region (original : Set Cell) (parent : Cell)
    (block : ∀ c ∈ PlusRefinement.unitSquare, Cell.add parent c ∈ original) :
    ∀ c ∈ isolationRing, Cell.add (Cell.scale 3 parent) c ∈ PlusRefinement.region original := by
  intro c hc
  obtain ⟨q, hq, r, hr, rfl⟩ :=
    (PlusRefinement.mem_polyomino _ _).mp (isolationRing_subset_refinement hc)
  refine ⟨Cell.add parent q, block q hq, r, hr, ?_⟩
  apply Prod.ext <;> dsimp [PlusRefinement.pixel, Cell.scale, Cell.add] <;> omega

private def inner (offset c : Cell) : Prop :=
  offset.1 + 1 ≤ c.1 ∧ c.1 ≤ offset.1 + 2 ∧
    offset.2 + 1 ≤ c.2 ∧ c.2 ≤ offset.2 + 2

theorem tile_nonempty {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) : (tile n holes).Nonempty :=
  ⟨(0, 0), unitSquare_subset_tile hn holes admissible (by decide)⟩

/-- A ring of refined holes isolates a 2-by-2 background component. The
reserved corner supplies a second component. -/
theorem tile_disconnected_of_ring {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (offset : Cell)
    (hx : 4 ≤ offset.1) (hy : 4 ≤ offset.2)
    (hx' : offset.1 + 3 < n) (hy' : offset.2 + 3 < n)
    (mx : offset.1 % 3 = 0) (my : offset.2 % 3 = 0)
    (ring_holes : ∀ c ∈ isolationRing, Cell.add offset c ∈ holes) :
    ¬ Polyomino.IsConnected (tile n holes) := by
  have anchor : Cell.add offset (1, 1) ∈ tile n holes := by
    apply lower_tile hn holes admissible
    refine Or.inl ⟨?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
    · dsimp [KeyCornerArithmetic.inBox, Cell.add]
      omega
    · dsimp [KeyCornerArithmetic.inVerticalLock, Cell.add]
      omega
    · dsimp [KeyCornerArithmetic.inHorizontalLock, Cell.add]
      omega
    · dsimp [Cell.add]
      omega
    · dsimp [Cell.add]
      omega
  apply Polyomino.not_connected_of_closed (tile n holes) {c | inner offset c} ?_
    (Cell.add offset (1, 1)) (0, 0) anchor
    (unitSquare_subset_tile hn holes admissible (by decide))
  · dsimp [inner, Cell.add]
    omega
  · dsimp [inner]
    omega
  · intro a _ inside b hb adjacent
    change inner offset a at inside
    change inner offset b
    by_contra outside
    have ring_member : Cell.sub b offset ∈ isolationRing := by
      have ax : a.1 = offset.1 + 1 ∨ a.1 = offset.1 + 2 := by unfold inner at inside; omega
      have ay : a.2 = offset.2 + 1 ∨ a.2 = offset.2 + 2 := by unfold inner at inside; omega
      simp only [isolationRing, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Cell.sub]
      unfold inner at inside outside
      unfold Cell.SideAdjacent at adjacent
      rcases ax with ax | ax <;> rcases ay with ay | ay
      all_goals
        rcases adjacent with ⟨h₁, h₂ | h₂⟩ | ⟨h₁, h₂ | h₂⟩ <;> omega
    have hole := ring_holes _ ring_member
    have cancel : Cell.add offset (Cell.sub b offset) = b := by
      apply Prod.ext <;> dsimp [Cell.add, Cell.sub] <;> omega
    rw [cancel] at hole
    have box : b ∈ square n := by
      rw [mem_square]
      unfold inner at inside
      unfold Cell.SideAdjacent at adjacent
      omega
    have background := (tile_representatives n holes).1 b hb
    rw [residue_of_mem_square box] at background
    exact background.2 hole

/-- A 2-by-2 block in the source, away from the period boundary, is enough
to certify disconnectedness of Q. -/
theorem tile_disconnected_of_source_square {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (original : Set Cell)
    (carrier : holesRegion n holes = PlusRefinement.region original) (parent : Cell)
    (hx : 4 ≤ 3 * parent.1) (hy : 4 ≤ 3 * parent.2)
    (hx' : 3 * parent.1 + 3 < n) (hy' : 3 * parent.2 + 3 < n)
    (block : ∀ c ∈ PlusRefinement.unitSquare, Cell.add parent c ∈ original) :
    ¬ Polyomino.IsConnected (tile n holes) := by
  apply tile_disconnected_of_ring hn holes admissible (Cell.scale 3 parent) hx hy hx' hy'
    (by simp [Cell.scale]) (by simp [Cell.scale])
  intro c hc
  have inside := ring_inside_refined_region original parent block c hc
  rw [← carrier] at inside
  change residue n (Cell.add (Cell.scale 3 parent) c) ∈ holes at inside
  have bounds : ∀ d ∈ isolationRing, 0 ≤ d.1 ∧ d.1 ≤ 3 ∧ 0 ≤ d.2 ∧ d.2 ≤ 3 := by decide
  have cb := bounds c hc
  have box : Cell.add (Cell.scale 3 parent) c ∈ square n := by
    rw [mem_square]
    dsimp [Cell.add, Cell.scale]
    omega
  rwa [residue_of_mem_square box] at inside

end LeanTrominoes.KeyedPeriodicComplement
