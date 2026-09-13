/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationGeometry
import LeanTrominoes.Theorem55Compiler
import LeanTrominoes.Theorem55StripUnaryCorrect

/-! # Existing tile compilers also compute the translation-only reductions -/

namespace LeanTrominoes.ThreeTranslationPolyominoes

theorem plane_forget (input : List Cell) (h : planeProblem input) : Theorem55.planeProblem input :=
  ⟨h.1,h.2.1,((translationTileable_iff _ _).mp h.2.2).tileable⟩

theorem strip_forget (input : Theorem55.StripInput) (h : stripProblem input) : Theorem55.stripProblem input :=
  ⟨h.1,h.2.1,h.2.2.1,((translationTileable_iff _ _).mp h.2.2.2).tileable⟩

theorem compile_plane_correct {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) :
    planeProblem (Theorem55Compiler.compile (Theorem55Compiler.sourceInput presentation)) ↔
      Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier := by
  constructor
  · intro h
    exact (Theorem55Compiler.compile_source_correct presentation).mp (plane_forget _ h)
  · intro h
    have old := (Theorem55Compiler.compile_source_correct presentation).mpr h
    refine ⟨old.1,old.2.1,?_⟩
    rw [Theorem55Compiler.compile_source]
    exact plane_of_source (by have := Theorem55Source.period_large presentation; omega)
      _ _ (Theorem55Source.holes_carrier presentation)
      ((Theorem55Source.tileable_iff presentation).mpr h)

theorem compile_strip_correct (source : PeriodicStrip) (valid : source.IsWellFormed) :
    stripProblem (Theorem55StripUnary.compiledInput source) ↔ PeriodicStripTrominoTiling .I source := by
  constructor
  · intro h
    exact (Theorem55StripUnary.compiledInput_correct source valid).mp (strip_forget _ h)
  · intro h
    have old := (Theorem55StripUnary.compiledInput_correct source valid).mpr h
    refine ⟨old.1,old.2.1,old.2.2.1,?_⟩
    rw [Theorem55StripUnary.compiled_tile source valid]
    change TranslationTileable _ (horizontalStrip (3 * Theorem55StripSource.period source))
    exact strip_of_source (n := 3 * Theorem55StripSource.period source) (by have := Theorem55StripSource.period_large source valid.2.1; omega)
      _ _ (Theorem55StripSource.holes_carrier source valid.2.1)
      ((Theorem55StripSource.tileable_iff source).mpr h.2)

end LeanTrominoes.ThreeTranslationPolyominoes
