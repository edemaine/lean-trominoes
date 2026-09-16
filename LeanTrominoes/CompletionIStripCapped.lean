/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIStripPrefill
import LeanTrominoes.CompletionStripCappedCore

/-! # Capped-strip correctness for a blank-padded I-brick palette -/
namespace LeanTrominoes.CompletionPattern.IBricks

theorem capped_strip_iff_plane (palette : Cell → Fin 24) (count : Int) (hn : 0 < count)
    (blank : ∀ location, location.2 ≤ 0 ∨ count ≤ location.2 → palette location = 0) :
    Tromino.I.Completable (StripCaps.cappedRegion (162*count))
      (bandPrescribed palette count ∪ StripCaps.shellPrefill .I (162*count)) ↔
      Tromino.I.Completable Set.univ (globalPrescribed palette) := by
  rw [StripCaps.capped_completion_iff .I (162*count) (by omega)
    (bandPrescribed palette count) (band_prescribed_inside palette count)]
  exact core_completion_iff_plane palette count hn blank

end LeanTrominoes.CompletionPattern.IBricks
