/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseRoutedClauseDescriptorData

/-! # Semantics of normalized routed-clause descriptor blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedBaseRoutedSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedBaseRoutedSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The base stream is exactly one current-slice polarity descriptor for
each direct source clause, in source presentation order. -/
theorem directRetainedPlanarMetadataBaseRoutedClauseDescriptors_eq_semantic
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataBaseRoutedClauseDescriptors decider symbols =
      (directSourceFormula decider symbols).clauses.map fun clause =>
        FormulaShapeRetainedPlanarMetadataDirection.routedClauseDescriptor
          (clause.map fun literal =>
            (⟨false, literal.value⟩ : LiteralProfile)) := by
  let source := directSourceFormula decider symbols
  let sourceProfiles := directSourceFormulaClauseProfiles decider symbols
  let emit := fun profiles : List LiteralProfile =>
    [FormulaShapeRetainedPlanarMetadataDirection.routedClauseDescriptor
      (currentizeRoutedLiteralProfiles profiles)]
  calc
    directRetainedPlanarMetadataBaseRoutedClauseDescriptors decider symbols =
        sourceProfiles.flatMap fun profile => emit profile.literals := by
      rfl
    _ = (sourceProfiles.map ClauseProfile.literals).flatMap emit := by
      rw [List.flatMap_map]
    _ = (source.clauses.map
          ClauseProfileOccurrenceSplit.literalProfiles).flatMap emit := by
      simpa [source, directSourceFormula] using congrArg
        (List.flatMap emit)
        (directSourceFormulaClauseProfiles_literals_eq decider symbols)
    _ = source.clauses.map fun clause =>
          FormulaShapeRetainedPlanarMetadataDirection.routedClauseDescriptor
            (clause.map fun literal =>
              (⟨false, literal.value⟩ : LiteralProfile)) := by
      induction source.clauses with
      | nil => rfl
      | cons clause clauses induction =>
          simp only [List.map_cons, List.flatMap_cons]
          rw [induction]
          unfold emit currentizeRoutedLiteralProfiles
            ClauseProfileOccurrenceSplit.literalProfiles
          simp [List.map_map, Function.comp_def]

end LeanTrominoes.PeriodicCNFStripReduction

end
