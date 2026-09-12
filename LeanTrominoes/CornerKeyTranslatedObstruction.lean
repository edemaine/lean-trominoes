/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CornerKeyObstruction

/-! # The right lock obstruction in world coordinates -/

namespace LeanTrominoes.KeyedPeriodicComplement

/-- The right corner patch reflected about the y-axis. -/
def reflectedRightPatch : Polyomino := rightPatch.image SquareSymmetry.reflectY.act

/-- Move the reflected corner to the right edge of a square of side n. -/
def rightWorldPatch (n : Nat) : Polyomino :=
  reflectedRightPatch.image (Cell.add ((n : Int) - 1, 0))

private def mirrorSymmetry : SquareSymmetry → SquareSymmetry
  | .identity => .reflectY
  | .rotate90 => .reflectDiagonal
  | .rotate180 => .reflectX
  | .rotate270 => .reflectAntidiagonal
  | .reflectX => .rotate180
  | .reflectDiagonal => .rotate90
  | .reflectY => .identity
  | .reflectAntidiagonal => .rotate270

private def mirror (p : Placement Unit) : Placement Unit :=
  {p with symmetry := mirrorSymmetry p.symmetry, offset := (-p.offset.1, p.offset.2)}

private theorem mem_mirror (c : Cell) (p : Placement Unit) :
    c ∈ (mirror p).cells (fun _ => PlusRefinement.bumpy) ↔
      SquareSymmetry.reflectY.act c ∈ p.cells (fun _ => PlusRefinement.bumpy) := by
  simp only [Placement.mem_cells_iff]
  constructor <;> rintro ⟨q, hq, he⟩ <;> refine ⟨q, hq, ?_⟩ <;>
    cases hs : p.symmetry <;>
    simp only [mirror, hs, mirrorSymmetry, SquareSymmetry.act, Cell.add, Prod.ext_iff] at he ⊢ <;>
    constructor <;> omega

private theorem reflected_obstruction (p : Placement Unit)
    (cover : (-3, 2) ∈ p.cells (fun _ => PlusRefinement.bumpy)) :
    ¬ Disjoint reflectedRightPatch (p.cells (fun _ => PlusRefinement.bumpy)) := by
  have mirrored : (3, 2) ∈ (mirror p).cells (fun _ => PlusRefinement.bumpy) :=
    (mem_mirror _ _).mpr cover
  intro disjoint
  apply bumpy_cannot_fill_right_lock (mirror p) mirrored
  rw [Finset.disjoint_left] at disjoint ⊢
  intro c hc hp
  exact disjoint (Finset.mem_image.mpr ⟨c, hc, rfl⟩) ((mem_mirror c p).mp hp)

private def relative (offset : Cell) (p : Placement Unit) : Placement Unit :=
  {p with offset := Cell.sub p.offset offset}

private theorem mem_relative (offset c : Cell) (p : Placement Unit) :
    c ∈ (relative offset p).cells (fun _ => PlusRefinement.bumpy) ↔
      Cell.add offset c ∈ p.cells (fun _ => PlusRefinement.bumpy) := by
  simp only [Placement.mem_cells_iff]
  constructor <;> rintro ⟨source, hs, he⟩ <;> refine ⟨source, hs, ?_⟩ <;>
    simp only [relative, Cell.add, Cell.sub, Prod.ext_iff] at he ⊢ <;>
    constructor <;> omega

/-- No P can fill the right lock at any period, without overlapping its patch. -/
theorem bumpy_cannot_fill_right_world (n : Nat) (p : Placement Unit)
    (covers : ((n : Int) - 4, 2) ∈ p.cells (fun _ => PlusRefinement.bumpy)) :
    ¬ Disjoint (rightWorldPatch n) (p.cells (fun _ => PlusRefinement.bumpy)) := by
  let offset : Cell := ((n : Int) - 1, 0)
  have cover : (-3, 2) ∈ (relative offset p).cells (fun _ => PlusRefinement.bumpy) := by
    apply (mem_relative _ _ _).mpr
    have eq : Cell.add offset (-3, 2) = ((n : Int) - 4, 2) := by
      apply Prod.ext <;> dsimp [offset, Cell.add] <;> omega
    rwa [eq]
  intro disjoint
  apply reflected_obstruction (relative offset p) cover
  rw [Finset.disjoint_left] at disjoint ⊢
  intro c hc hp
  exact disjoint (Finset.mem_image.mpr ⟨c, hc, rfl⟩) ((mem_relative offset c p).mp hp)

end LeanTrominoes.KeyedPeriodicComplement
