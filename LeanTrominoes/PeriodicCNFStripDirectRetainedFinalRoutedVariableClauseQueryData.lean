/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRoutedVariableQueryPostprocess
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataNormalizedRoutedVariableDescriptorData

/-! # Direct final routed-variable clause-query streams -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedVariableQueryDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Replace every normalized routed-variable metadata template by its stable
direct query. -/
def directRetainedFinalCompiledRoutedVariableClauseQueries
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  (directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
    decider symbols).flatMap
      retainedFinalDirectRoutedVariableQueryBlock

/-- One stable six-query routed-variable site per original source literal. -/
def directRetainedFinalRoutedVariableClauseQueries
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  (List.range (PeriodicCNF.presentationLiteralCount
    (PeriodicThreeCNF.formula
      (PolySpaceCompiler.formulaOfSymbols decider symbols)))).flatMap
        fun _targetIndex =>
          retainedFinalDirectRoutedVariableFullSiteQueries

abbrev DirectRetainedFinalCompiledRoutedVariableClauseQueryCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalCompiledRoutedVariableClauseQueries decider)

abbrev DirectRetainedFinalRoutedVariableClauseQueryCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalRoutedVariableClauseQueries decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
