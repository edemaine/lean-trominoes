/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripUnaryTileGeometry

/-! # Correctness of the polynomial-time two-tile strip compiler -/

namespace LeanTrominoes.Theorem55StripUnary

theorem compiled_tile (source : PeriodicStrip) (valid : source.IsWellFormed) :
    (compiledInput source).2.toFinset =
      KeyedStripComplement.tile (side source) (Theorem55StripSource.holes source) := by
  change (((ordinaryTable.rows source).map natCell) ++ leftKeyCells).toFinset = _
  rw [List.toFinset_append,ordinaryTable_cells source valid,leftKeyCells_image]
  ext c
  constructor
  · intro hc
    rcases Finset.mem_union.mp hc with ordinary | moved
    · obtain ⟨hb,hl⟩ := Finset.mem_sdiff.mp ordinary
      exact Finset.mem_image.mpr ⟨c,hb,by simp [KeyedStripComplement.repack,hl]⟩
    · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp moved
      exact Finset.mem_image.mpr ⟨p,horizontalLock_background source valid.2.1 hp,
        by simpa [KeyedStripComplement.repack,hp] using he⟩
  · intro hc
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hc
    by_cases lock : p ∈ KeyedPeriodicComplement.horizontalLock (side source)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨p,lock,by simp [KeyedStripComplement.repack,lock]⟩))
    · apply Finset.mem_union.mpr
      left
      simpa [KeyedStripComplement.repack,lock] using Finset.mem_sdiff.mpr ⟨hp,lock⟩

/-- The actual polynomial-time emitted input has exactly the source tiling semantics. -/
theorem compiledInput_correct (source : PeriodicStrip) (valid : source.IsWellFormed) :
    Theorem55.stripProblem (compiledInput source) ↔ PeriodicStripTrominoTiling .I source := by
  have semantic := Theorem55StripSource.stripProblem_iff source valid.2.1
    (compiledInput source).2 (compiled_tile source valid)
  simpa only [PeriodicStripTrominoTiling,valid,true_and,compiledInput,side] using semantic

end LeanTrominoes.Theorem55StripUnary
