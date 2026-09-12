/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PlusRefinement

/-!
# The fixed 15-omino cannot tile the plane

The two cells `(1, 1)` and `(2, 1)` form a pocket above the first two
crosses. After fixing a tile, the possible tiles covering either pocket
cell are a finite list. The local certificates below are checked by the
Lean kernel and include all eight square symmetries.
-/

namespace LeanTrominoes.PlusRefinement

private abbrev family : Unit → Polyomino := fun _ => bumpy

/-- A tile covering `target`, specified by its orientation and the source
cell that covers `target`. -/
def coveringPlacement (target : Cell) (symmetry : SquareSymmetry) (source : Cell) :
    Placement Unit := ⟨(), symmetry, Cell.sub target (symmetry.act source)⟩

/-- The finite list of possible placements covering a given cell. -/
def coveringPlacements (target : Cell) : Finset (Placement Unit) :=
  Finset.univ.biUnion fun symmetry => bumpy.image (coveringPlacement target symmetry)

theorem mem_coveringPlacements (p : Placement Unit) (target : Cell) :
    p ∈ coveringPlacements target ↔ target ∈ p.cells family := by
  simp only [coveringPlacements, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Placement.mem_cells_iff]
  constructor
  · rintro ⟨s, c, hc, rfl⟩
    refine ⟨c, hc, ?_⟩
    simp [coveringPlacement, Cell.add, Cell.sub]
  · rintro ⟨c, hc, eq⟩
    refine ⟨p.symmetry, c, hc, ?_⟩
    apply Placement.ext
    · exact Subsingleton.elim _ _
    · rfl
    · simp only [coveringPlacement, Cell.sub]
      simp only [Cell.add, Prod.ext_iff] at eq
      apply Prod.ext <;> dsimp <;> omega

/-- The reference tile with the given orientation, centered at the origin. -/
private def reference (s : SquareSymmetry) : Placement Unit := ⟨(), s, (0, 0)⟩

/-- Candidates that do not overlap the fixed reference tile. -/
private def pocketCandidates (s : SquareSymmetry) (c : Cell) :
    Finset (Placement Unit) :=
  (coveringPlacements (s.act c)).filter fun p =>
    Disjoint ((reference s).cells family) (p.cells family)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem first_pocket_certificate :
    ∀ s : SquareSymmetry, ∀ p ∈ pocketCandidates s (1, 1),
      s.act (1, 2) ∈ p.cells family ∧ s.act (2, 1) ∉ p.cells family := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem second_pocket_certificate :
    ∀ s : SquareSymmetry, ∀ p ∈ pocketCandidates s (2, 1),
      s.act (1, 2) ∈ p.cells family := by
  decide

private theorem pockets_outside :
    ∀ s : SquareSymmetry,
      s.act (1, 1) ∉ (reference s).cells family ∧
      s.act (2, 1) ∉ (reference s).cells family := by decide

/-- Express a placement relative to an arbitrary origin. -/
private def relative (origin : Cell) (p : Placement Unit) : Placement Unit :=
  {p with offset := Cell.sub p.offset origin}

private theorem mem_relative (origin c : Cell) (p : Placement Unit) :
    c ∈ (relative origin p).cells family ↔ Cell.add origin c ∈ p.cells family := by
  simp only [Placement.mem_cells_iff]
  constructor <;> rintro ⟨source, hs, he⟩ <;> refine ⟨source, hs, ?_⟩ <;>
    simp only [relative, Cell.add, Cell.sub, Prod.ext_iff] at he ⊢ <;>
    constructor <;> omega

private theorem relative_self (p : Placement Unit) :
    relative p.offset p = reference p.symmetry := by
  apply Placement.ext
  · exact Subsingleton.elim _ _
  · rfl
  · simp [relative, reference, Cell.sub]

private theorem disjoint_relative (origin : Cell) (p q : Placement Unit)
    (h : Disjoint (p.cells family) (q.cells family)) :
    Disjoint ((relative origin p).cells family) ((relative origin q).cells family) := by
  rw [Finset.disjoint_left] at h ⊢
  intro c hp hq
  exact h ((mem_relative origin c p).mp hp) ((mem_relative origin c q).mp hq)

/-- The 15-omino cannot tile the plane, even with rotations and reflections. -/
theorem bumpy_not_tileable_plane : ¬ TileableBy bumpy Set.univ := by
  rintro ⟨placements, tiling⟩
  obtain ⟨base, hbase, -⟩ := tiling.exists_cover (Set.mem_univ (0, 0))
  let s := base.symmetry
  obtain ⟨a, ha, hca⟩ := tiling.exists_cover
    (Set.mem_univ (Cell.add base.offset (s.act (1, 1))))
  obtain ⟨b, hb, hcb⟩ := tiling.exists_cover
    (Set.mem_univ (Cell.add base.offset (s.act (2, 1))))
  have ra : s.act (1, 1) ∈ (relative base.offset a).cells family :=
    (mem_relative _ _ _).mpr hca
  have rb : s.act (2, 1) ∈ (relative base.offset b).cells family :=
    (mem_relative _ _ _).mpr hcb
  have nea : base ≠ a := by
    intro eq
    subst a
    rw [relative_self] at ra
    exact (pockets_outside s).1 ra
  have neb : base ≠ b := by
    intro eq
    subst b
    rw [relative_self] at rb
    exact (pockets_outside s).2 rb
  have da := disjoint_relative base.offset base a (tiling.disjoint_cells hbase ha nea)
  have db := disjoint_relative base.offset base b (tiling.disjoint_cells hbase hb neb)
  rw [relative_self] at da db
  have ac : relative base.offset a ∈ pocketCandidates s (1, 1) :=
    Finset.mem_filter.mpr ⟨(mem_coveringPlacements _ _).mpr ra, da⟩
  have bc : relative base.offset b ∈ pocketCandidates s (2, 1) :=
    Finset.mem_filter.mpr ⟨(mem_coveringPlacements _ _).mpr rb, db⟩
  obtain ⟨sharedA, excludesB⟩ := first_pocket_certificate s _ ac
  have sharedB := second_pocket_certificate s _ bc
  have neab : a ≠ b := by
    rintro rfl
    exact excludesB rb
  have disjointAB := disjoint_relative base.offset a b (tiling.disjoint_cells ha hb neab)
  exact (Finset.disjoint_left.mp disjointAB) sharedA sharedB

end LeanTrominoes.PlusRefinement
