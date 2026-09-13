/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TranslationStripRaw

/-! # The orientation-restricted strip decision predicate -/

namespace LeanTrominoes.TranslationStrip
open Theorem55StripDecider

def decideStripRaw (input : Theorem55.StripInput) : Bool :=
  decide (0 < input.1) && decide (input.2 ≠ []) &&
    PolyominoConnectivitySearch.disconnectedPacked input.2 &&
      tilingCheck (rawCells input) input.1 (bound input)

theorem decideStripRaw_correct (input : Theorem55.StripInput) :
    decideStripRaw input = true ↔ ThreeTranslationPolyominoes.stripProblem input := by
  have bounded : PolyominoStripWindow.Bounded (PolyominoStripWindow.Raw.tiles (rawCells input)) (bound input) := by
    rw [rawCells_tiles]
    exact tiles_bounded input
  have tiling : tilingCheck (rawCells input) input.1 (bound input) = true ↔
      TranslationTileable (ThreeTranslationPolyominoes.tiles input.2.toFinset) (horizontalStrip input.1) := by
    rw [tilingCheck_correct _ _ _ bounded,rawCells_tiles]
    exact (ThreeTranslationPolyominoes.translationTileable_iff _ _).symm
  simp only [decideStripRaw,Bool.and_eq_true,decide_eq_true_eq,tiling]
  by_cases nonempty : input.2 = []
  · simp [nonempty,ThreeTranslationPolyominoes.stripProblem]
  · rw [PolyominoConnectivitySearch.disconnectedPacked_correct _ nonempty]
    simp [ThreeTranslationPolyominoes.stripProblem,nonempty,and_assoc]

end LeanTrominoes.TranslationStrip
