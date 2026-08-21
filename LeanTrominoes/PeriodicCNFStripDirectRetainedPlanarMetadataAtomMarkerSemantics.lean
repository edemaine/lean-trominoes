/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataAtomMarkerData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeSemantics

/-! # Exact direct retained metadata source-atom markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

/-- Extracting variable tokens from any formula shape gives a constant marker
word whose length is the shape's distinct-variable count. -/
theorem flatMap_retainedAtomMarkerBlock (shape : List FormulaShape.Token) :
    shape.flatMap retainedAtomMarkerBlock =
      List.replicate (FormulaShape.variableCount shape)
        FormulaShapeDirectionOrdering.Token.variable := by
  induction shape with
  | nil => rfl
  | cons token shape induction =>
      cases token <;>
        simp [retainedAtomMarkerBlock, FormulaShape.variableCount,
          FormulaShape.variableMarkers, induction, List.replicate_succ]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedAtomMarkerSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The extracted marker word contains exactly one marker per distinct
variable of the guarded direct source formula. -/
theorem directRetainedPlanarMetadataAtomMarkers_eq_replicate
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataAtomMarkers decider symbols =
      List.replicate
        (sourceFormula
          (PolySpaceCompiler.formulaOfSymbols
            decider symbols)).variableOccurrences.dedup.length
        .variable := by
  unfold directRetainedPlanarMetadataAtomMarkers
  rw [flatMap_retainedAtomMarkerBlock]
  rw [(directSourceFormulaShape_correct decider symbols).2]

end LeanTrominoes.PeriodicCNFStripReduction
