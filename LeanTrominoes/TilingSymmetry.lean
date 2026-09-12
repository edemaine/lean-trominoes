/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingTranslation

/-! # Reorienting plane tilings by square symmetries -/

namespace LeanTrominoes
namespace SquareSymmetry

/-- Composition, with the right symmetry acting first. -/
def compose : SquareSymmetry → SquareSymmetry → SquareSymmetry
  | .identity, .identity
  | .rotate90, .rotate270
  | .rotate180, .rotate180
  | .rotate270, .rotate90
  | .reflectX, .reflectX
  | .reflectDiagonal, .reflectDiagonal
  | .reflectY, .reflectY
  | .reflectAntidiagonal, .reflectAntidiagonal => .identity
  | .identity, .rotate90
  | .rotate90, .identity
  | .rotate180, .rotate270
  | .rotate270, .rotate180
  | .reflectX, .reflectAntidiagonal
  | .reflectDiagonal, .reflectX
  | .reflectY, .reflectDiagonal
  | .reflectAntidiagonal, .reflectY => .rotate90
  | .identity, .rotate180
  | .rotate90, .rotate90
  | .rotate180, .identity
  | .rotate270, .rotate270
  | .reflectX, .reflectY
  | .reflectDiagonal, .reflectAntidiagonal
  | .reflectY, .reflectX
  | .reflectAntidiagonal, .reflectDiagonal => .rotate180
  | .identity, .rotate270
  | .rotate90, .rotate180
  | .rotate180, .rotate90
  | .rotate270, .identity
  | .reflectX, .reflectDiagonal
  | .reflectDiagonal, .reflectY
  | .reflectY, .reflectAntidiagonal
  | .reflectAntidiagonal, .reflectX => .rotate270
  | .identity, .reflectX
  | .rotate90, .reflectAntidiagonal
  | .rotate180, .reflectY
  | .rotate270, .reflectDiagonal
  | .reflectX, .identity
  | .reflectDiagonal, .rotate90
  | .reflectY, .rotate180
  | .reflectAntidiagonal, .rotate270 => .reflectX
  | .identity, .reflectDiagonal
  | .rotate90, .reflectX
  | .rotate180, .reflectAntidiagonal
  | .rotate270, .reflectY
  | .reflectX, .rotate270
  | .reflectDiagonal, .identity
  | .reflectY, .rotate90
  | .reflectAntidiagonal, .rotate180 => .reflectDiagonal
  | .identity, .reflectY
  | .rotate90, .reflectDiagonal
  | .rotate180, .reflectX
  | .rotate270, .reflectAntidiagonal
  | .reflectX, .rotate180
  | .reflectDiagonal, .rotate270
  | .reflectY, .identity
  | .reflectAntidiagonal, .rotate90 => .reflectY
  | .identity, .reflectAntidiagonal
  | .rotate90, .reflectY
  | .rotate180, .reflectDiagonal
  | .rotate270, .reflectX
  | .reflectX, .rotate90
  | .reflectDiagonal, .rotate180
  | .reflectY, .rotate270
  | .reflectAntidiagonal, .identity => .reflectAntidiagonal

theorem act_compose (s t : SquareSymmetry) (c : Cell) :
    (s.compose t).act c = s.act (t.act c) := by
  cases s <;> cases t <;> rcases c with ⟨x, y⟩ <;> simp [compose, act]

@[simp] theorem compose_identity (s : SquareSymmetry) : s.compose .identity = s := by
  cases s <;> rfl

@[simp] theorem compose_inverse_cancel (s t : SquareSymmetry) :
    s.compose (s.inverse.compose t) = t := by
  cases s <;> cases t <;> rfl

@[simp] theorem act_zero (s : SquareSymmetry) : s.act (0, 0) = (0, 0) := by
  cases s <;> rfl

theorem act_add (s : SquareSymmetry) (a b : Cell) :
    s.act (Cell.add a b) = Cell.add (s.act a) (s.act b) := by
  cases s <;> apply Prod.ext <;> dsimp [act, Cell.add] <;> omega

end SquareSymmetry

namespace Placement

/-- Apply a square symmetry to an entire placed copy. -/
def orient {ι : Type*} (s : SquareSymmetry) (p : Placement ι) : Placement ι :=
  ⟨p.kind, s.compose p.symmetry, s.act p.offset⟩

@[simp] theorem orient_cancel {ι : Type*} (s : SquareSymmetry) (p : Placement ι) :
    (p.orient s.inverse).orient s = p := by
  apply Placement.ext
  · rfl
  · exact SquareSymmetry.compose_inverse_cancel s p.symmetry
  · exact SquareSymmetry.act_inverse_act s p.offset

theorem orient_injective {ι : Type*} (s : SquareSymmetry) :
    Function.Injective (orient (ι := ι) s) := by
  intro a b h
  have eq := congrArg (orient s.inverse) h
  have hi : s.inverse.inverse = s := by cases s <;> rfl
  have cancel (p : Placement ι) : (p.orient s).orient s.inverse = p := by
    have result := orient_cancel s.inverse p
    rwa [hi] at result
  simpa only [cancel] using eq

theorem mem_orient_cells {ι : Type*} (tiles : ι → Polyomino)
    (s : SquareSymmetry) (p : Placement ι) (c : Cell) :
    s.act c ∈ (p.orient s).cells tiles ↔ c ∈ p.cells tiles := by
  simp only [mem_cells_iff, orient, SquareSymmetry.act_compose, ← SquareSymmetry.act_add,
    SquareSymmetry.act_injective s |>.eq_iff]

end Placement

/-- View a plane tiling in an arbitrarily reoriented coordinate system. -/
theorem IsTiling.reorient {ι : Type*} {tiles : ι → Polyomino}
    {placements : Set (Placement ι)} (tiling : IsTiling tiles Set.univ placements)
    (s : SquareSymmetry) : IsTiling tiles Set.univ {p | p.orient s ∈ placements} := by
  constructor
  · intro _ _ _ _
    trivial
  · intro c _
    obtain ⟨a, ⟨ha, covers⟩, unique⟩ := tiling.uniqueCover (s.act c) (Set.mem_univ _)
    let p := a.orient s.inverse
    have oriented : p.orient s = a := Placement.orient_cancel s a
    have member : p.orient s ∈ placements := oriented ▸ ha
    have pc : c ∈ p.cells tiles := by
      apply (Placement.mem_orient_cells tiles s p c).mp
      rwa [oriented]
    refine ⟨p, ⟨member, pc⟩, ?_⟩
    intro b hb
    apply Placement.orient_injective s
    rw [oriented]
    exact unique (b.orient s)
      ⟨hb.1, (Placement.mem_orient_cells tiles s b c).mpr hb.2⟩

end LeanTrominoes
