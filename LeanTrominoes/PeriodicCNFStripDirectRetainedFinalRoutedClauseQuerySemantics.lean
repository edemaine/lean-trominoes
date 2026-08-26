/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedClauseQueryData

/-! # Correctness of direct final routed-clause queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedClauseQuerySemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedClauseQuerySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Compiled finite clause profiles emit exactly one current-slice routed
query per clause of the direct geometric source. -/
theorem directRetainedFinalRoutedClauseQueries_eq_sourceClauses
    (symbols : List encoding.Γ) :
    directRetainedFinalRoutedClauseQueries decider symbols =
      (directSourceFormula decider symbols).clauses.map fun clause =>
        retainedFinalDirectRoutedClauseQuery
          (clause.map fun literal =>
            (⟨false, literal.value⟩ : LiteralProfile)) := by
  let source := directSourceFormula decider symbols
  let sourceProfiles := directSourceFormulaClauseProfiles decider symbols
  let emit := fun profiles : List LiteralProfile =>
    [retainedFinalDirectRoutedClauseQuery
      (currentizeRoutedLiteralProfiles profiles)]
  calc
    directRetainedFinalRoutedClauseQueries decider symbols =
        sourceProfiles.flatMap fun profile => emit profile.literals := by
      rfl
    _ = (sourceProfiles.map ClauseProfile.literals).flatMap emit := by
      rw [List.flatMap_map]
    _ = (source.clauses.map
          ClauseProfileOccurrenceSplit.literalProfiles).flatMap emit := by
      have profilesEq :=
        directSourceFormulaClauseProfiles_literals_eq decider symbols
      change sourceProfiles.map ClauseProfile.literals =
        source.clauses.map
          ClauseProfileOccurrenceSplit.literalProfiles at profilesEq
      exact congrArg (List.flatMap emit) profilesEq
    _ = source.clauses.map fun clause =>
          retainedFinalDirectRoutedClauseQuery
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
