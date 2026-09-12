/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyCornerGeometry

/-! # Compressing a corner neighborhood to a fixed-size arithmetic check -/

namespace LeanTrominoes.KeyCornerArithmetic

/-- Keep the ends of a coordinate interval and retain only the residue in
its middle. The reference square has side length 96. -/
def compress (n x : Int) : Int :=
  if x < 36 then x else if n - 36 ≤ x then x - n + 96 else 45 + x % 3

theorem low_compress (n x d k : Int) (hn : 96 ≤ n)
    (hd : -16 ≤ d ∧ d ≤ 16) (hk : -6 ≤ k ∧ k ≤ 19) :
    (x + d ≤ k ↔ compress n x + d ≤ k) ∧
    (k ≤ x + d ↔ k ≤ compress n x + d) ∧
    (x + d < k ↔ compress n x + d < k) ∧
    (x + d = k ↔ compress n x + d = k) := by
  unfold compress
  split
  · simp
  · split <;> omega

theorem high_compress (n x d k : Int) (hn : 96 ≤ n)
    (hd : -16 ≤ d ∧ d ≤ 16) (hk : -19 ≤ k ∧ k ≤ 6) :
    (x + d ≤ n + k ↔ compress n x + d ≤ 96 + k) ∧
    (n + k ≤ x + d ↔ 96 + k ≤ compress n x + d) ∧
    (x + d < n + k ↔ compress n x + d < 96 + k) ∧
    (x + d = n + k ↔ compress n x + d = 96 + k) := by
  unfold compress
  split <;> try split
  all_goals omega

theorem mod_compress (n x d : Int) (hn : n % 3 = 0) :
    (x + d) % 3 = (compress n x + d) % 3 := by
  unfold compress
  split <;> try split
  all_goals omega

theorem upper_compress (n x y dx dy : Int) (hn : 96 ≤ n)
    (hx : -16 ≤ dx ∧ dx ≤ 16) (hy : -16 ≤ dy ∧ dy ≤ 16) :
    upper n (x + dx, y + dy) ↔
      upper 96 (compress n x + dx, compress n y + dy) := by
  obtain ⟨xlown4le, xlown4ge, xlown4lt, xlown4eq⟩ := low_compress n x dx (-4) hn hx (by decide)
  obtain ⟨xlown1le, xlown1ge, xlown1lt, xlown1eq⟩ := low_compress n x dx (-1) hn hx (by decide)
  obtain ⟨xlow0le, xlow0ge, xlow0lt, xlow0eq⟩ := low_compress n x dx (0) hn hx (by decide)
  obtain ⟨xlow2le, xlow2ge, xlow2lt, xlow2eq⟩ := low_compress n x dx (2) hn hx (by decide)
  obtain ⟨xlow3le, xlow3ge, xlow3lt, xlow3eq⟩ := low_compress n x dx (3) hn hx (by decide)
  obtain ⟨xlow18le, xlow18ge, xlow18lt, xlow18eq⟩ := low_compress n x dx (18) hn hx (by decide)
  obtain ⟨xhighn18le, xhighn18ge, xhighn18lt, xhighn18eq⟩ := high_compress n x dx (-18) hn hx (by decide)
  obtain ⟨xhighn4le, xhighn4ge, xhighn4lt, xhighn4eq⟩ := high_compress n x dx (-4) hn hx (by decide)
  obtain ⟨xhigh0le, xhigh0ge, xhigh0lt, xhigh0eq⟩ := high_compress n x dx (0) hn hx (by decide)
  obtain ⟨xhigh2le, xhigh2ge, xhigh2lt, xhigh2eq⟩ := high_compress n x dx (2) hn hx (by decide)
  obtain ⟨xhigh3le, xhigh3ge, xhigh3lt, xhigh3eq⟩ := high_compress n x dx (3) hn hx (by decide)
  obtain ⟨ylown4le, ylown4ge, ylown4lt, ylown4eq⟩ := low_compress n y dy (-4) hn hy (by decide)
  obtain ⟨ylown1le, ylown1ge, ylown1lt, ylown1eq⟩ := low_compress n y dy (-1) hn hy (by decide)
  obtain ⟨ylow0le, ylow0ge, ylow0lt, ylow0eq⟩ := low_compress n y dy (0) hn hy (by decide)
  obtain ⟨ylow2le, ylow2ge, ylow2lt, ylow2eq⟩ := low_compress n y dy (2) hn hy (by decide)
  obtain ⟨ylow3le, ylow3ge, ylow3lt, ylow3eq⟩ := low_compress n y dy (3) hn hy (by decide)
  obtain ⟨ylow18le, ylow18ge, ylow18lt, ylow18eq⟩ := low_compress n y dy (18) hn hy (by decide)
  obtain ⟨yhighn18le, yhighn18ge, yhighn18lt, yhighn18eq⟩ := high_compress n y dy (-18) hn hy (by decide)
  obtain ⟨yhighn4le, yhighn4ge, yhighn4lt, yhighn4eq⟩ := high_compress n y dy (-4) hn hy (by decide)
  obtain ⟨yhigh0le, yhigh0ge, yhigh0lt, yhigh0eq⟩ := high_compress n y dy (0) hn hy (by decide)
  obtain ⟨yhigh2le, yhigh2ge, yhigh2lt, yhigh2eq⟩ := high_compress n y dy (2) hn hy (by decide)
  obtain ⟨yhigh3le, yhigh3ge, yhigh3lt, yhigh3eq⟩ := high_compress n y dy (3) hn hy (by decide)
  simp_all [upper, inBox, inVerticalLock, inHorizontalLock, inKey, Int.sub_eq_add_neg]

theorem lower_compress (n x y dx dy : Int) (hn : 96 ≤ n) (period : n % 3 = 0)
    (hx : -16 ≤ dx ∧ dx ≤ 16) (hy : -16 ≤ dy ∧ dy ≤ 16) :
    lower n (x + dx, y + dy) ↔
      lower 96 (compress n x + dx, compress n y + dy) := by
  obtain ⟨xlown4le, xlown4ge, xlown4lt, xlown4eq⟩ := low_compress n x dx (-4) hn hx (by decide)
  obtain ⟨xlown1le, xlown1ge, xlown1lt, xlown1eq⟩ := low_compress n x dx (-1) hn hx (by decide)
  obtain ⟨xlow0le, xlow0ge, xlow0lt, xlow0eq⟩ := low_compress n x dx (0) hn hx (by decide)
  obtain ⟨xlow2le, xlow2ge, xlow2lt, xlow2eq⟩ := low_compress n x dx (2) hn hx (by decide)
  obtain ⟨xlow3le, xlow3ge, xlow3lt, xlow3eq⟩ := low_compress n x dx (3) hn hx (by decide)
  obtain ⟨xlow18le, xlow18ge, xlow18lt, xlow18eq⟩ := low_compress n x dx (18) hn hx (by decide)
  obtain ⟨xhighn18le, xhighn18ge, xhighn18lt, xhighn18eq⟩ := high_compress n x dx (-18) hn hx (by decide)
  obtain ⟨xhighn4le, xhighn4ge, xhighn4lt, xhighn4eq⟩ := high_compress n x dx (-4) hn hx (by decide)
  obtain ⟨xhigh0le, xhigh0ge, xhigh0lt, xhigh0eq⟩ := high_compress n x dx (0) hn hx (by decide)
  obtain ⟨xhigh2le, xhigh2ge, xhigh2lt, xhigh2eq⟩ := high_compress n x dx (2) hn hx (by decide)
  obtain ⟨xhigh3le, xhigh3ge, xhigh3lt, xhigh3eq⟩ := high_compress n x dx (3) hn hx (by decide)
  obtain ⟨ylown4le, ylown4ge, ylown4lt, ylown4eq⟩ := low_compress n y dy (-4) hn hy (by decide)
  obtain ⟨ylown1le, ylown1ge, ylown1lt, ylown1eq⟩ := low_compress n y dy (-1) hn hy (by decide)
  obtain ⟨ylow0le, ylow0ge, ylow0lt, ylow0eq⟩ := low_compress n y dy (0) hn hy (by decide)
  obtain ⟨ylow2le, ylow2ge, ylow2lt, ylow2eq⟩ := low_compress n y dy (2) hn hy (by decide)
  obtain ⟨ylow3le, ylow3ge, ylow3lt, ylow3eq⟩ := low_compress n y dy (3) hn hy (by decide)
  obtain ⟨ylow18le, ylow18ge, ylow18lt, ylow18eq⟩ := low_compress n y dy (18) hn hy (by decide)
  obtain ⟨yhighn18le, yhighn18ge, yhighn18lt, yhighn18eq⟩ := high_compress n y dy (-18) hn hy (by decide)
  obtain ⟨yhighn4le, yhighn4ge, yhighn4lt, yhighn4eq⟩ := high_compress n y dy (-4) hn hy (by decide)
  obtain ⟨yhigh0le, yhigh0ge, yhigh0lt, yhigh0eq⟩ := high_compress n y dy (0) hn hy (by decide)
  obtain ⟨yhigh2le, yhigh2ge, yhigh2lt, yhigh2eq⟩ := high_compress n y dy (2) hn hy (by decide)
  obtain ⟨yhigh3le, yhigh3ge, yhigh3lt, yhigh3eq⟩ := high_compress n y dy (3) hn hy (by decide)
  have xm := mod_compress n x dx period
  have ym := mod_compress n y dy period
  simp_all [lower, inBox, inVerticalLock, inHorizontalLock, inKey, Int.sub_eq_add_neg]

end LeanTrominoes.KeyCornerArithmetic
