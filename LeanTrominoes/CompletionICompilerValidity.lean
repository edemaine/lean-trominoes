/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIOrientationCompiler
import LeanTrominoes.CompletionIPrefillValidity

/-! # The compiler always outputs a valid periodic partial tiling -/

namespace LeanTrominoes.CompletionPattern.IBricks

theorem compileDrawing_valid (drawing : Gadget.PeriodicOrthogonalDrawing) :
    Tromino.I.IsPartialTiling Set.univ ((compileDrawing drawing).prescribed .I) := by
  unfold compileDrawing
  rw [PeriodicPattern.compileSquare_prescribed _ _ (macro_palette_periodic drawing)]
  exact global_prefill_valid _

theorem compileDrawing_full_rank (drawing : Gadget.PeriodicOrthogonalDrawing) :
    ((compileDrawing drawing).occupiedRegion .I).IsFullRank :=
  PeriodicPattern.compileSquare_full_rank _ _

end LeanTrominoes.CompletionPattern.IBricks
