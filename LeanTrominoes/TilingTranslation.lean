/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling
import Lean.Elab.Tactic.Omega

/-! # Translation of plane tilings -/

namespace LeanTrominoes

namespace Placement

/-- Translate a placement, preserving its prototile and orientation. -/
def shift {ι : Type*} (offset : Cell) (p : Placement ι) : Placement ι :=
  ⟨p.kind, p.symmetry, Cell.add offset p.offset⟩

theorem shift_injective {ι : Type*} (offset : Cell) :
    Function.Injective (shift (ι := ι) offset) := by
  intro a b h
  apply Placement.ext
  · simpa only [shift] using congrArg (fun p : Placement ι => p.kind) h
  · simpa only [shift] using congrArg (fun p : Placement ι => p.symmetry) h
  · exact Cell.add_left_injective offset (congrArg Placement.offset h)

@[simp] theorem shift_cancel {ι : Type*} (offset : Cell) (p : Placement ι) :
    (p.shift (Cell.sub (0, 0) offset)).shift offset = p := by
  apply Placement.ext
  · rfl
  · rfl
  · apply Prod.ext <;> dsimp [shift, Cell.add, Cell.sub] <;> omega

theorem mem_shift_cells {ι : Type*} (tiles : ι → Polyomino)
    (offset : Cell) (p : Placement ι) (c : Cell) :
    Cell.add offset c ∈ (p.shift offset).cells tiles ↔ c ∈ p.cells tiles := by
  simp only [mem_cells_iff]
  constructor
  · rintro ⟨q, hq, eq⟩
    refine ⟨q, hq, ?_⟩
    apply Cell.add_left_injective offset
    simpa only [shift, Cell.add, Int.add_assoc] using eq
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q, hq, ?_⟩
    simp only [shift, Cell.add, Int.add_assoc]

end Placement

/-- View a plane tiling from an arbitrary translated origin. -/
theorem IsTiling.recenter {ι : Type*} {tiles : ι → Polyomino}
    {placements : Set (Placement ι)} (tiling : IsTiling tiles Set.univ placements)
    (offset : Cell) : IsTiling tiles Set.univ {p | p.shift offset ∈ placements} := by
  constructor
  · intro _ _ _ _
    trivial
  · intro c _
    obtain ⟨a, ⟨ha, covers⟩, unique⟩ :=
      tiling.uniqueCover (Cell.add offset c) (Set.mem_univ _)
    let p := a.shift (Cell.sub (0, 0) offset)
    have shifted : p.shift offset = a := Placement.shift_cancel offset a
    have member : p.shift offset ∈ placements := shifted ▸ ha
    have pc : c ∈ p.cells tiles := by
      apply (Placement.mem_shift_cells tiles offset p c).mp
      rwa [shifted]
    refine ⟨p, ⟨member, pc⟩, ?_⟩
    intro b hb
    apply Placement.shift_injective offset
    rw [shifted]
    exact unique (b.shift offset)
      ⟨hb.1, (Placement.mem_shift_cells tiles offset b c).mpr hb.2⟩

end LeanTrominoes
