/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLStripPrefill
import LeanTrominoes.CompletionStripCappedCore

/-! # Capped-strip correctness for a blank-padded L-brick palette -/
namespace LeanTrominoes.CompletionPattern.LBricks

theorem capped_strip_iff_plane (palette : Cell → Fin 24) (count : Int) (hn : 0 < count)
    (blank : ∀ location, location.2 ≤ 0 ∨ count ≤ location.2 → palette location = 0) :
    Tromino.L.Completable (StripCaps.cappedRegion (36*count))
      (bandPrescribed palette count ∪ StripCaps.shellPrefill .L (36*count)) ↔
      Tromino.L.Completable Set.univ (globalPrescribed palette) := by
  rw [StripCaps.capped_completion_iff .L (36*count) (by omega)
    (bandPrescribed palette count) (band_prescribed_inside palette count)]
  exact core_completion_iff_plane palette count hn blank

end LeanTrominoes.CompletionPattern.LBricks
