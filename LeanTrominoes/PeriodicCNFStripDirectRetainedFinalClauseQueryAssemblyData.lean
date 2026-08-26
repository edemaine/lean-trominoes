/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalCrossoverClauseQueryData
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalFallbackClauseQueryData
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedClauseQueryData
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedVariableClauseQueryData

/-! # Five-family assembly of final copied-clause queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalQueryAssemblyDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct routed-clause queries followed by direct routed-variable queries. -/
def directRetainedFinalRoutedClauseQuerySuffix
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  directRetainedFinalRoutedClauseQueries decider symbols ++
    directRetainedFinalRoutedVariableClauseQueries decider symbols

/-- Fallback bend queries followed by the two direct routed families. -/
def directRetainedFinalBendClauseQuerySuffix
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  directRetainedFinalBendClauseQueries decider symbols ++
    directRetainedFinalRoutedClauseQuerySuffix decider symbols

/-- Fallback carrier queries followed by all three normalized families. -/
def directRetainedFinalCarrierClauseQuerySuffix
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  directRetainedFinalCarrierClauseQueries decider symbols ++
    directRetainedFinalBendClauseQuerySuffix decider symbols

/-- The five retained quotient families in final clause-presentation order. -/
def directRetainedFinalClauseQueryAssembly
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  directRetainedFinalCrossoverClauseQueries decider symbols ++
    directRetainedFinalCarrierClauseQuerySuffix decider symbols

abbrev DirectRetainedFinalRoutedClauseQuerySuffixCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalRoutedClauseQuerySuffix decider)

abbrev DirectRetainedFinalBendClauseQuerySuffixCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalBendClauseQuerySuffix decider)

abbrev DirectRetainedFinalCarrierClauseQuerySuffixCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalCarrierClauseQuerySuffix decider)

abbrev DirectRetainedFinalClauseQueryAssemblyCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalClauseQueryAssembly decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
