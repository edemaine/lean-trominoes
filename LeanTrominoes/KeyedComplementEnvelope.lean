/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPeriodicComplement
import LeanTrominoes.KeyCornerGeometry

/-! # The actual keyed tile lies between the corner-matching envelopes -/

namespace LeanTrominoes.KeyedPeriodicComplement

/-- The holes stay on the cross grid and avoid all four reserved corners. -/
def AdmissibleHoles (n : Nat) (holes : Polyomino) : Prop :=
  ∀ c ∈ holes,
    (c.1 % 3 = 0 ∨ c.2 % 3 = 0) ∧
      ¬ ((c.1 < 18 ∨ (n : Int) - 18 ≤ c.1) ∧
        (c.2 < 18 ∨ (n : Int) - 18 ≤ c.2))

theorem verticalLock_iff (c : Cell) :
    c ∈ verticalLock ↔ KeyCornerArithmetic.inVerticalLock c := by
  simp only [verticalLock, KeyCornerArithmetic.inVerticalLock,
    Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  omega

theorem horizontalLock_iff (n : Nat) (c : Cell) :
    c ∈ horizontalLock n ↔ KeyCornerArithmetic.inHorizontalLock n c := by
  simp only [horizontalLock, KeyCornerArithmetic.inHorizontalLock,
    Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  omega

/-- Every cell of Q lies in the full keyed-square envelope. -/
theorem tile_upper {n : Nat} (hn : 96 ≤ n) (holes : Polyomino) {q : Cell}
    (hq : q ∈ tile n holes) : KeyCornerArithmetic.upper n q := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
  have box := (mem_square _ _).mp (Finset.mem_sdiff.mp hc).1
  unfold repack
  split
  · rename_i hv
    have hv := (verticalLock_iff c).mp hv
    apply Or.inr
    dsimp [KeyCornerArithmetic.inKey, Cell.add]
    unfold KeyCornerArithmetic.inVerticalLock at hv
    omega
  · rename_i hv
    split
    · rename_i hh
      have hh := (horizontalLock_iff n c).mp hh
      apply Or.inr
      dsimp [KeyCornerArithmetic.inKey, Cell.add]
      unfold KeyCornerArithmetic.inHorizontalLock at hh
      omega
    · rename_i hh
      exact Or.inl ⟨box, fun h => hv ((verticalLock_iff c).mpr h),
        fun h => hh ((horizontalLock_iff n c).mpr h)⟩

private theorem vertical_background {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) {c : Cell} (hc : c ∈ verticalLock) :
    c ∈ background n holes := by
  have h := (verticalLock_iff c).mp hc
  unfold KeyCornerArithmetic.inVerticalLock at h
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [mem_square]
    omega
  · intro member
    have corner := (admissible c member).2
    apply corner
    omega

private theorem horizontal_background {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) {c : Cell} (hc : c ∈ horizontalLock n) :
    c ∈ background n holes := by
  have h := (horizontalLock_iff n c).mp hc
  unfold KeyCornerArithmetic.inHorizontalLock at h
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [mem_square]
    omega
  · intro member
    have corner := (admissible c member).2
    apply corner
    omega

private theorem vertical_key_mem {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) {c : Cell} (hc : c ∈ verticalLock) :
    Cell.add c (0, n) ∈ tile n holes := by
  refine Finset.mem_image.mpr ⟨c, vertical_background hn holes admissible hc, ?_⟩
  simp [repack, hc]

private theorem horizontal_key_mem {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) {c : Cell} (hc : c ∈ horizontalLock n) :
    Cell.add c (-(n : Int), 0) ∈ tile n holes := by
  have hv : c ∉ verticalLock := by
    rw [verticalLock_iff]
    have hh := (horizontalLock_iff n c).mp hc
    unfold KeyCornerArithmetic.inVerticalLock KeyCornerArithmetic.inHorizontalLock at *
    omega
  refine Finset.mem_image.mpr ⟨c, horizontal_background hn holes admissible hc, ?_⟩
  simp [repack, hv, hc]

private theorem key_mem {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) {q : Cell} (hq : KeyCornerArithmetic.inKey n q) :
    q ∈ tile n holes := by
  have vertical (h : KeyCornerArithmetic.inVerticalLock (q.1, q.2 - n)) :
      q ∈ tile n holes := by
    have mem := vertical_key_mem hn holes admissible ((verticalLock_iff _).mpr h)
    simpa [Cell.add] using mem
  have horizontal (h : KeyCornerArithmetic.inHorizontalLock n (q.1 + n, q.2)) :
      q ∈ tile n holes := by
    have mem := horizontal_key_mem hn holes admissible ((horizontalLock_iff _ _).mpr h)
    simpa [Cell.add] using mem
  rcases hq with h | h | h | h
  · apply vertical
    unfold KeyCornerArithmetic.inVerticalLock
    dsimp
    omega
  · apply vertical
    unfold KeyCornerArithmetic.inVerticalLock
    dsimp
    omega
  · apply horizontal
    unfold KeyCornerArithmetic.inHorizontalLock
    dsimp
    omega
  · apply horizontal
    unfold KeyCornerArithmetic.inHorizontalLock
    dsimp
    omega

/-- The cross-grid background and solid corners are present in the actual Q. -/
theorem lower_tile {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) {q : Cell} (hq : KeyCornerArithmetic.lower n q) :
    q ∈ tile n holes := by
  rcases hq with ⟨box, hv, hh, occupied⟩ | key
  · have outside : q ∉ holes := by
      intro member
      obtain ⟨grid, corner⟩ := admissible q member
      rcases occupied with offGrid | inCorner
      · rcases grid with hx | hy
        · exact offGrid.1 hx
        · exact offGrid.2 hy
      · exact corner inCorner
    have bg : q ∈ background n holes :=
      Finset.mem_sdiff.mpr ⟨(mem_square n q).mpr box, outside⟩
    refine Finset.mem_image.mpr ⟨q, bg, ?_⟩
    have v : q ∉ verticalLock := fun h => hv ((verticalLock_iff _).mp h)
    have h : q ∉ horizontalLock n := fun h => hh ((horizontalLock_iff _ _).mp h)
    simp [repack, v, h]
  · exact key_mem hn holes admissible key

end LeanTrominoes.KeyedPeriodicComplement
