/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementEnvelope
import LeanTrominoes.TilingStripStack

/-! # A horizontally keyed complement with flat strip boundaries -/

namespace LeanTrominoes.KeyedStripComplement

open KeyedPeriodicComplement (square mem_square background horizontalLock)

/-- Reduce only the unbounded coordinate. -/
def residue (n : Nat) (c : Cell) : Cell := (c.1 % (n : Int), c.2)

/-- Move the right lock to the left, keeping both strip boundaries flat. -/
def repack (n : Nat) (c : Cell) : Cell :=
  if c ∈ horizontalLock n then Cell.add c (-(n : Int), 0) else c

def tile (n : Nat) (holes : Polyomino) : Polyomino :=
  (background n holes).image (repack n)

def holesRegion (n : Nat) (holes : Polyomino) : Set Cell :=
  {c | c ∈ horizontalStrip n ∧ residue n c ∈ holes}

def gridPlacements (n : Nat) : Set (Placement Unit) :=
  {p | p.symmetry = .identity ∧ ∃ i : Int, p.offset = ((n : Int) * i, 0)}

theorem residue_repack (n : Nat) (c : Cell) : residue n (repack n c) = residue n c := by
  unfold repack
  split <;> simp [residue, Cell.add]

theorem residue_of_mem_square {n : Nat} {c : Cell} (hc : c ∈ square n) :
    residue n c = c := by
  obtain ⟨hx₀, hx₁, _, _⟩ := (mem_square _ _).mp hc
  exact Prod.ext (Int.emod_eq_of_lt hx₀ hx₁) rfl

theorem residue_mem_square {n : Nat} (hn : 0 < n) {c : Cell}
    (hc : c ∈ horizontalStrip n) : residue n c ∈ square n := by
  rw [mem_square]
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega), hc⟩

theorem tile_bounds (n : Nat) (holes : Polyomino) {q : Cell} (hq : q ∈ tile n holes) :
    -4 ≤ q.1 ∧ q.1 < n ∧ 0 ≤ q.2 ∧ q.2 < n := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := (mem_square _ _).mp (Finset.mem_sdiff.mp hc).1
  unfold repack
  split
  · rename_i hh
    simp only [horizontalLock, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hh
    dsimp [Cell.add]
    omega
  · omega

theorem tile_representatives (n : Nat) (holes : Polyomino) :
    (∀ q ∈ tile n holes, residue n q ∈ square n ∧ residue n q ∉ holes) ∧
    (∀ c ∈ square n, c ∉ holes → ∃! q, q ∈ tile n holes ∧ residue n q = c) := by
  have canonical (c : Cell) (hc : c ∈ background n holes) :
      residue n (repack n c) = c := by
    rw [residue_repack, residue_of_mem_square (Finset.mem_sdiff.mp hc).1]
  constructor
  · intro q hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
    rw [canonical c hc]
    exact Finset.mem_sdiff.mp hc
  · intro c hc hhole
    have hb : c ∈ background n holes := Finset.mem_sdiff.mpr ⟨hc, hhole⟩
    refine ⟨repack n c, ⟨Finset.mem_image.mpr ⟨c, hb, rfl⟩, canonical c hb⟩, ?_⟩
    rintro q ⟨hq, he⟩
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    rw [canonical d hd] at he
    exact congrArg (repack n) he

private theorem residue_translate (n : Nat) (i : Int) (c : Cell) :
    residue n (Cell.add ((n : Int) * i, 0) c) = residue n c := by
  simp [residue, Cell.add, Int.add_emod]

/-- Canonical horizontal copies cover precisely the complement within the strip. -/
theorem grid_tiling {n : Nat} (hn : 0 < n) (holes : Polyomino) :
    IsTiling (fun _ : Unit => tile n holes)
      (horizontalStrip n \ holesRegion n holes) (gridPlacements n) := by
  obtain ⟨valid, representative⟩ := tile_representatives n holes
  constructor
  · rintro p ⟨hs, i, hp⟩ c hc
    obtain ⟨q, hq, rfl⟩ := (Placement.mem_cells_iff _ _ _).mp hc
    have bounds := tile_bounds n holes hq
    constructor
    · simpa [horizontalStrip, hs, hp, SquareSymmetry.act, Cell.add] using bounds.2.2
    · intro mem
      have bad := mem.2
      rw [hs, hp, SquareSymmetry.act, residue_translate] at bad
      exact (valid q hq).2 bad
  · intro c hc
    have outside : residue n c ∉ holes := fun h => hc.2 ⟨hc.1,h⟩
    obtain ⟨q, ⟨hq, hres⟩, unique⟩ :=
      representative (residue n c) (residue_mem_square hn hc.1) outside
    let p : Placement Unit := ⟨(), .identity, Cell.sub c q⟩
    have heq : (n : Int) * (c.1 / n - q.1 / n) = c.1 - q.1 ∧ q.2 = c.2 := by
      have hx := congrArg Prod.fst hres
      have hy := congrArg Prod.snd hres
      dsimp [residue] at hx hy
      have cx := Int.emod_add_mul_ediv c.1 (n : Int)
      have qx := Int.emod_add_mul_ediv q.1 (n : Int)
      constructor
      · rw [mul_sub]; omega
      · exact hy
    have hp : p ∈ gridPlacements n :=
      ⟨rfl, c.1 / n - q.1 / n, Prod.ext heq.1.symm (by dsimp [p,Cell.sub]; omega)⟩
    have covers : c ∈ p.cells (fun _ => tile n holes) := by
      apply (Placement.mem_cells_iff _ _ _).mpr
      refine ⟨q, hq, ?_⟩
      simp [p, Cell.add, Cell.sub, SquareSymmetry.act]
    refine ⟨p, ⟨hp, covers⟩, ?_⟩
    rintro other ⟨⟨hs, i, hoff⟩, hcover⟩
    obtain ⟨r, hr, he⟩ := (Placement.mem_cells_iff _ _ _).mp hcover
    have residueEq : residue n r = residue n c := by
      rw [← he, hs, hoff, SquareSymmetry.act, residue_translate]
    have eq := unique r ⟨hr, residueEq⟩
    subst r
    apply Placement.ext
    · exact Subsingleton.elim _ _
    · exact hs
    · have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      simp only [hs, SquareSymmetry.act, Cell.add] at hx hy
      apply Prod.ext <;> dsimp [p, Cell.sub] <;> omega

end LeanTrominoes.KeyedStripComplement
