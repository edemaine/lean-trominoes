/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PlusRefinement
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

/-!
# The keyed periodic complement

Figure 16's vertical and horizontal keys are obtained by moving five cells
from the top and right boundaries to the opposite boundaries. Repacking
fundamental-domain representatives this way preserves the periodic union
and disjointness of the canonical translates. This file proves that forward
construction; it does not assert that arbitrary tilings force these translates.
-/

namespace LeanTrominoes.KeyedPeriodicComplement

/-- Reduction modulo a square period, with representatives in `[0, n)²`. -/
def residue (n : Nat) (c : Cell) : Cell := (c.1 % (n : Int), c.2 % (n : Int))

/-- The square fundamental domain of side length `n`. -/
def square (n : Nat) : Polyomino :=
  (Finset.range n ×ˢ Finset.range n).image fun p => ((p.1 : Int), (p.2 : Int))

theorem mem_square (n : Nat) (c : Cell) :
    c ∈ square n ↔ 0 ≤ c.1 ∧ c.1 < n ∧ 0 ≤ c.2 ∧ c.2 < n := by
  simp only [square, Finset.mem_image, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    dsimp
    omega
  · rintro ⟨hx₀, hx₁, hy₀, hy₁⟩
    exact ⟨(c.1.toNat, c.2.toNat), ⟨by omega, by omega⟩, Prod.ext (by simpa) (by simpa)⟩

theorem residue_mem_square {n : Nat} (hn : 0 < n) (c : Cell) :
    residue n c ∈ square n := by
  rw [mem_square]
  have positive : (0 : Int) < n := by omega
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ positive,
    Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ positive⟩

theorem residue_of_mem_square {n : Nat} {c : Cell} (hc : c ∈ square n) :
    residue n c = c := by
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := (mem_square _ _).mp hc
  apply Prod.ext <;> simp only [residue]
  · exact Int.emod_eq_of_lt hx₀ hx₁
  · exact Int.emod_eq_of_lt hy₀ hy₁

/-- The vertical lock at the top left, with its asymmetric side tooth. -/
def verticalLock : Polyomino := {(2, 0), (2, 1), (2, 2), (2, 3), (3, 2)}

/-- The horizontal lock at the top right, with its hooked end. -/
def horizontalLock (n : Nat) : Polyomino :=
  {((n : Int) - 4, 2), ((n : Int) - 4, 3), ((n : Int) - 3, 3),
    ((n : Int) - 2, 3), ((n : Int) - 1, 3)}

/-- Move the two locks to become the complementary keys on the opposite sides. -/
def repack (n : Nat) (c : Cell) : Cell :=
  if c ∈ verticalLock then Cell.add c (0, n)
  else if c ∈ horizontalLock n then Cell.add c (-(n : Int), 0)
  else c

theorem residue_repack (n : Nat) (c : Cell) :
    residue n (repack n c) = residue n c := by
  unfold repack
  split
  · simp [residue, Cell.add]
  · split
    · simp [residue, Cell.add]
    · rfl

/-- The finite background in one period, excluding the cells to be tiled by P. -/
def background (n : Nat) (holes : Polyomino) : Polyomino := square n \ holes

/-- The input-dependent tile Q, including its corner keys. -/
def tile (n : Nat) (holes : Polyomino) : Polyomino :=
  (background n holes).image (repack n)

/-- The keys add only four cells to each side-length of the bounding box. -/
theorem tile_bounds (n : Nat) (holes : Polyomino) {q : Cell} (hq : q ∈ tile n holes) :
    -4 ≤ q.1 ∧ q.1 < n ∧ 0 ≤ q.2 ∧ q.2 < (n : Int) + 4 := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := (mem_square _ _).mp (Finset.mem_sdiff.mp hc).1
  unfold repack
  split
  · rename_i hv
    simp only [verticalLock, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hv
    dsimp [Cell.add]
    omega
  · split
    · rename_i hh
      simp only [horizontalLock, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hh
      dsimp [Cell.add]
      omega
    · omega

/-- Repacking chooses exactly one representative for each background residue. -/
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

/-- The periodically repeated holes that remain available for the small tile. -/
def holesRegion (n : Nat) (holes : Polyomino) : Set Cell :=
  {c | residue n c ∈ holes}

/-- All canonical translates of Q, with no rotations. -/
def gridPlacements (n : Nat) : Set (Placement Unit) :=
  {p | p.symmetry = .identity ∧ ∃ i j : Int, p.offset = ((n : Int) * i, (n : Int) * j)}

private theorem residue_translate (n : Nat) (i j : Int) (c : Cell) :
    residue n (Cell.add ((n : Int) * i, (n : Int) * j) c) = residue n c := by
  simp [residue, Cell.add, Int.add_emod]

/-- The keyed tile's canonical translates tile exactly the periodic complement. -/
theorem grid_tiling {n : Nat} (hn : 0 < n) (holes : Polyomino) :
    IsTiling (fun _ : Unit => tile n holes) (holesRegion n holes)ᶜ (gridPlacements n) := by
  obtain ⟨valid, representative⟩ := tile_representatives n holes
  constructor
  · rintro p ⟨hs, i, j, hp⟩ c hc
    obtain ⟨q, hq, rfl⟩ := (Placement.mem_cells_iff _ _ _).mp hc
    change residue n (Cell.add p.offset (p.symmetry.act q)) ∉ holes
    rw [hs, hp, SquareSymmetry.act, residue_translate]
    exact (valid q hq).2
  · intro c hc
    obtain ⟨q, ⟨hq, hres⟩, unique⟩ :=
      representative (residue n c) (residue_mem_square hn c) hc
    let p : Placement Unit := ⟨(), .identity, Cell.sub c q⟩
    have heq : (n : Int) * (c.1 / n - q.1 / n) = c.1 - q.1 ∧
        (n : Int) * (c.2 / n - q.2 / n) = c.2 - q.2 := by
      have hx := congrArg Prod.fst hres
      have hy := congrArg Prod.snd hres
      dsimp [residue] at hx hy
      have cx := Int.emod_add_mul_ediv c.1 (n : Int)
      have cy := Int.emod_add_mul_ediv c.2 (n : Int)
      have qx := Int.emod_add_mul_ediv q.1 (n : Int)
      have qy := Int.emod_add_mul_ediv q.2 (n : Int)
      constructor <;> rw [mul_sub] <;> omega
    have hp : p ∈ gridPlacements n :=
      ⟨rfl, c.1 / n - q.1 / n, c.2 / n - q.2 / n, Prod.ext heq.1.symm heq.2.symm⟩
    have covers : c ∈ p.cells (fun _ => tile n holes) := by
      apply (Placement.mem_cells_iff _ _ _).mpr
      refine ⟨q, hq, ?_⟩
      simp [p, Cell.add, Cell.sub, SquareSymmetry.act]
    refine ⟨p, ⟨hp, covers⟩, ?_⟩
    rintro other ⟨⟨hs, i, j, hoff⟩, hcover⟩
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

end LeanTrominoes.KeyedPeriodicComplement
