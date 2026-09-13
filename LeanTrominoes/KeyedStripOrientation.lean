/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedStripComplement
import LeanTrominoes.TilingPair

/-! # Boundary constraints on the horizontally keyed strip tile -/

namespace LeanTrominoes.KeyedStripComplement
open KeyedPeriodicComplement (AdmissibleHoles mem_square horizontalLock_iff)
open KeyCornerArithmetic (inBox inHorizontalLock)

def inKey (c : Cell) : Prop :=
  (c.1 = -4 ∧ c.2 = 2) ∨ (-4 ≤ c.1 ∧ c.1 ≤ -1 ∧ c.2 = 3)

def upper (n : Int) (c : Cell) : Prop :=
  (inBox n c ∧ ¬ inHorizontalLock n c) ∨ inKey c

def lower (n : Int) (c : Cell) : Prop :=
  (inBox n c ∧ ¬ inHorizontalLock n c ∧
    ((c.1 % 3 ≠ 0 ∧ c.2 % 3 ≠ 0) ∨
      ((c.1 < 18 ∨ n - 18 ≤ c.1) ∧ (c.2 < 18 ∨ n - 18 ≤ c.2)))) ∨ inKey c

theorem tile_upper (n : Nat) (holes : Polyomino) {q : Cell}
    (hq : q ∈ tile n holes) : upper n q := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
  have box := (mem_square _ _).mp (Finset.mem_sdiff.mp hc).1
  unfold repack
  split
  · rename_i hh
    have hh := (horizontalLock_iff n c).mp hh
    right
    dsimp [inKey, Cell.add]
    unfold inHorizontalLock at hh
    omega
  · rename_i hh
    exact Or.inl ⟨box, fun h => hh ((horizontalLock_iff n c).mpr h)⟩

theorem lower_tile {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) {c : Cell} (hc : lower n c) : c ∈ tile n holes := by
  rcases hc with ⟨box, unlocked, solid⟩ | key
  · have outside : c ∉ holes := by
      intro h
      have a := admissible c h
      rcases solid with grid | corner
      · rcases a.1 with h | h
        · exact grid.1 h
        · exact grid.2 h
      · exact a.2 corner
    refine Finset.mem_image.mpr ⟨c, Finset.mem_sdiff.mpr ⟨(mem_square _ _).mpr box,outside⟩, ?_⟩
    have h : c ∉ KeyedPeriodicComplement.horizontalLock n := fun h => unlocked ((horizontalLock_iff n c).mp h)
    simp [repack, h]
  · let d : Cell := (c.1 + n, c.2)
    have lock : d ∈ KeyedPeriodicComplement.horizontalLock n := by
      rw [horizontalLock_iff]
      dsimp [d,inHorizontalLock]
      rcases key with key | key <;> omega
    have box : d ∈ KeyedPeriodicComplement.square n := by
      rw [mem_square]
      dsimp [d]
      rcases key with key | key <;> omega
    have outside : d ∉ holes := by
      intro h
      apply (admissible d h).2
      dsimp [d]
      rcases key with key | key <;> omega
    refine Finset.mem_image.mpr ⟨d,Finset.mem_sdiff.mpr ⟨box,outside⟩,?_⟩
    simp [repack,lock,d,Cell.add]

theorem corner_mem {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) {c : Cell}
    (box : inBox n c) (unlocked : ¬ inHorizontalLock n c)
    (corner : (c.1 < 18 ∨ (n : Int) - 18 ≤ c.1) ∧ (c.2 < 18 ∨ (n : Int) - 18 ≤ c.2)) :
    c ∈ tile n holes := lower_tile hn holes admissible (Or.inl ⟨box,unlocked,Or.inr corner⟩)

/-- Q cannot stand across the strip; its full height fixes its vertical offset. -/
theorem placement_orientation {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (p : Placement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => tile n holes), c ∈ horizontalStrip n) :
    (p.symmetry = .identity ∧ p.offset.2 = 0) ∨
    (p.symmetry = .reflectY ∧ p.offset.2 = 0) ∨
    (p.symmetry = .reflectX ∧ p.offset.2 = (n : Int) - 1) ∨
    (p.symmetry = .rotate180 ∧ p.offset.2 = (n : Int) - 1) := by
  have bounds (c : Cell) (h : c ∈ tile n holes) :=
    inside (Cell.add p.offset (p.symmetry.act c)) ((Placement.mem_cells_iff _ _ _).mpr ⟨c,h,rfl⟩)
  have a := bounds (0,0) (corner_mem hn holes admissible (by dsimp [inBox]; omega)
    (by dsimp [inHorizontalLock]; omega) (by dsimp; omega))
  have b := bounds (0,(n : Int)-1) (corner_mem hn holes admissible (by dsimp [inBox]; omega)
    (by dsimp [inHorizontalLock]; omega) (by dsimp; omega))
  have c := bounds ((n : Int)-1,0) (corner_mem hn holes admissible (by dsimp [inBox]; omega)
    (by dsimp [inHorizontalLock]; omega) (by dsimp; omega))
  have d := bounds (-4,2) (lower_tile hn holes admissible (Or.inr (by simp [inKey])))
  cases hs : p.symmetry <;> simp [horizontalStrip, hs, SquareSymmetry.act, Cell.add] at a b c d ⊢ <;> omega

end LeanTrominoes.KeyedStripComplement
