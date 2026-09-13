/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedStripGeometry
import LeanTrominoes.Theorem55StripSourceMask

/-! # The semantic strip target and its prepared-source equivalence -/

namespace LeanTrominoes.Theorem55

/-- A strip height and an explicit cell list for the disconnected tile. -/
abbrev StripInput := Nat × List Cell

/-- The full strip must have positive height and Q must be nonempty and disconnected. -/
def stripProblem (input : StripInput) : Prop :=
  0 < input.1 ∧ input.2.toFinset.Nonempty ∧ ¬ Polyomino.IsConnected input.2.toFinset ∧
    Tileable (pairTiles PlusRefinement.bumpy input.2.toFinset) (horizontalStrip input.1)

end LeanTrominoes.Theorem55

namespace LeanTrominoes.Theorem55StripSource

theorem stripProblem_iff (source : PeriodicStrip) (positive : 0 < source.period) (input : List Cell)
    (encoding : input.toFinset = KeyedStripComplement.tile (3 * period source) (holes source)) :
    Theorem55.stripProblem (3 * period source,input) ↔ Tromino.I.Tileable source.carrier := by
  have large := period_large source positive
  have admissible := holes_admissible source positive
  have carrier := holes_carrier source positive
  have nonempty := KeyedStripComplement.tile_nonempty (by omega : 96 ≤ 3 * period source) _ admissible
  have disconnected := KeyedStripComplement.tile_disconnected_of_source_square
    (by omega : 96 ≤ 3 * period source) _ admissible (region source) carrier (14,4)
    (by decide) (by decide) (by dsimp; omega) (by dsimp; omega) (source_square source positive)
  unfold Theorem55.stripProblem
  simp only [encoding, nonempty, disconnected, not_false_eq_true, true_and,
    show 0 < 3 * period source by omega]
  exact (KeyedStripComplement.pair_tileable_iff (by omega) (by omega) _ admissible _ carrier).trans
    (tileable_iff source)

end LeanTrominoes.Theorem55StripSource
