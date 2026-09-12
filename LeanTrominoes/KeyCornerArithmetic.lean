/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyCornerCompression
import LeanTrominoes.KeyCornerFinite

/-! # Uniform corner-key matching for arbitrary large periods -/

namespace LeanTrominoes.KeyCornerArithmetic

private theorem symmetry_bounds (s : SquareSymmetry) (c : Cell)
    (h : -16 ≤ c.1 ∧ c.1 ≤ 16 ∧ -16 ≤ c.2 ∧ c.2 ≤ 16) :
    (-16 ≤ (s.act c).1 ∧ (s.act c).1 ≤ 16) ∧
      (-16 ≤ (s.act c).2 ∧ (s.act c).2 ≤ 16) := by
  cases s <;> dsimp [SquareSymmetry.act] <;> omega

private theorem vertical_bounds :
    ∀ c ∈ verticalOffsets, -16 ≤ c.1 ∧ c.1 ≤ 16 ∧ -16 ≤ c.2 ∧ c.2 ≤ 16 := by decide

private theorem right_bounds :
    ∀ c ∈ rightOffsets, -16 ≤ c.1 ∧ c.1 ≤ 16 ∧ -16 ≤ c.2 ∧ c.2 ≤ 16 := by decide

private theorem compatible_compress (n : Int) (hn : 96 ≤ n) (period : n % 3 = 0)
    (s : SquareSymmetry) (c : Cell) (offsets : Finset Cell)
    (bounds : ∀ d ∈ offsets, -16 ≤ d.1 ∧ d.1 ≤ 16 ∧ -16 ≤ d.2 ∧ d.2 ≤ 16)
    (h : compatible n s c offsets) :
    compatible 96 s (compress n c.1, compress n c.2) offsets := by
  constructor
  · have eq := upper_compress n c.1 c.2 0 0 hn (by decide) (by decide)
    simp only [Int.add_zero, Prod.eta] at eq
    exact eq.mp h.1
  · intro d hd hl
    obtain ⟨hx, hy⟩ := symmetry_bounds s.inverse d (bounds d hd)
    have eq := lower_compress n c.1 c.2 (s.inverse.act d).1 (s.inverse.act d).2 hn period hx hy
    exact h.2 d hd (eq.mpr hl)

private theorem reference_bounds (c : Cell) (h : upper 96 c) :
    -4 ≤ c.1 ∧ c.1 < 100 ∧ -4 ≤ c.2 ∧ c.2 < 100 := by
  unfold upper inBox inVerticalLock inHorizontalLock inKey at h
  omega

private theorem reference_sound (offsets : Finset Cell) (result : Cell)
    (certificate : ∀ s : SquareSymmetry, ∀ x y : Fin 104,
      compatible 96 s ((x.val : Int) - 4, (y.val : Int) - 4) offsets →
        s = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = result)
    (s : SquareSymmetry) (c : Cell) (h : compatible 96 s c offsets) :
    s = .identity ∧ c = result := by
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := reference_bounds c h.1
  let x : Fin 104 := ⟨(c.1 + 4).toNat, by omega⟩
  let y : Fin 104 := ⟨(c.2 + 4).toNat, by omega⟩
  have hx : (x.val : Int) - 4 = c.1 := by dsimp [x]; omega
  have hy : (y.val : Int) - 4 = c.2 := by dsimp [y]; omega
  have input : compatible 96 s ((x.val : Int) - 4, (y.val : Int) - 4) offsets := by
    simpa only [hx, hy, Prod.eta] using h
  simpa only [hx, hy, Prod.eta] using certificate s x y input

/-- The only possible source cell at the vertical lock is the tip of the
bottom key, in the original orientation. -/
theorem vertical_source_match (n : Int) (hn : 96 ≤ n) (period : n % 3 = 0)
    (s : SquareSymmetry) (c : Cell) (h : compatible n s c verticalOffsets) :
    s = .identity ∧ c = (2, n + 3) := by
  obtain ⟨hs, hc⟩ := reference_sound verticalOffsets (2, 99) vertical_finite s _
    (compatible_compress n hn period s c verticalOffsets vertical_bounds h)
  refine ⟨hs, Prod.ext ?_ ?_⟩
  · have eq := (low_compress n c.1 0 2 hn (by decide) (by decide)).2.2.2
    have value := congrArg Prod.fst hc
    dsimp at value
    simpa only [Int.add_zero] using eq.mpr (by simpa using value)
  · have eq := (high_compress n c.2 0 3 hn (by decide) (by decide)).2.2.2
    have value := congrArg Prod.snd hc
    dsimp at value
    simpa only [Int.add_zero] using eq.mpr (by simpa using value)

/-- The only possible source cell at the right lock is the hooked end of
its left key, in the original orientation. -/
theorem right_source_match (n : Int) (hn : 96 ≤ n) (period : n % 3 = 0)
    (s : SquareSymmetry) (c : Cell) (h : compatible n s c rightOffsets) :
    s = .identity ∧ c = (-4, 2) := by
  obtain ⟨hs, hc⟩ := reference_sound rightOffsets (-4, 2) right_finite s _
    (compatible_compress n hn period s c rightOffsets right_bounds h)
  refine ⟨hs, Prod.ext ?_ ?_⟩
  · have eq := (low_compress n c.1 0 (-4) hn (by decide) (by decide)).2.2.2
    have value := congrArg Prod.fst hc
    dsimp at value
    simpa only [Int.add_zero] using eq.mpr (by simpa using value)
  · have eq := (low_compress n c.2 0 2 hn (by decide) (by decide)).2.2.2
    have value := congrArg Prod.snd hc
    dsimp at value
    simpa only [Int.add_zero] using eq.mpr (by simpa using value)

private theorem source_add (s : SquareSymmetry) (offset c d : Cell) :
    source s offset (Cell.add c d) = Cell.add (source s offset c) (s.inverse.act d) := by
  cases s <;> apply Prod.ext <;>
    dsimp [source, SquareSymmetry.inverse, SquareSymmetry.act, Cell.add, Cell.sub] <;> omega

/-- Covering the vertical lock without overlapping its occupied witnesses
forces the neighbor immediately above, without any rotation or reflection. -/
theorem vertical_match (n : Int) (hn : 96 ≤ n) (period : n % 3 = 0)
    (s : SquareSymmetry) (offset : Cell)
    (covers : upper n (source s offset (2, 3)))
    (avoids : ∀ d ∈ verticalOffsets, ¬ lower n (source s offset (Cell.add (2, 3) d))) :
    s = .identity ∧ offset = (0, -n) := by
  have compatible : compatible n s (source s offset (2, 3)) verticalOffsets := by
    refine ⟨covers, ?_⟩
    intro d hd
    simpa only [source_add] using avoids d hd
  obtain ⟨rfl, hc⟩ := vertical_source_match n hn period s _ compatible
  simp only [source, SquareSymmetry.inverse, SquareSymmetry.act, Cell.sub, Prod.mk.injEq] at hc
  exact ⟨rfl, Prod.ext (by dsimp; omega) (by dsimp; omega)⟩

/-- The right lock similarly forces the neighbor immediately to the right. -/
theorem right_match (n : Int) (hn : 96 ≤ n) (period : n % 3 = 0)
    (s : SquareSymmetry) (offset : Cell)
    (covers : upper n (source s offset (n - 4, 2)))
    (avoids : ∀ d ∈ rightOffsets, ¬ lower n (source s offset (Cell.add (n - 4, 2) d))) :
    s = .identity ∧ offset = (n, 0) := by
  have compatible : compatible n s (source s offset (n - 4, 2)) rightOffsets := by
    refine ⟨covers, ?_⟩
    intro d hd
    simpa only [source_add] using avoids d hd
  obtain ⟨rfl, hc⟩ := right_source_match n hn period s _ compatible
  simp only [source, SquareSymmetry.inverse, SquareSymmetry.act, Cell.sub, Prod.mk.injEq] at hc
  exact ⟨rfl, Prod.ext (by dsimp; omega) (by dsimp; omega)⟩

end LeanTrominoes.KeyCornerArithmetic
