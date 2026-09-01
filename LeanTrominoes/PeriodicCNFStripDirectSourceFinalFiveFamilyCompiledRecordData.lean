/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendCompiledBatchedRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierCompiledBatchedRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPhaseRouteTailRecordData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteTailRecordCompiler

/-! # Compiled five-family direct final routed records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFiveFamilyCompiledRecordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Expand the compiled crossover input records to final header/tail records. -/
def directSourceFinalCrossoverBatchedRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  HorizontalRoutedRouteTailRecord.batchedRecords
    (directSourceFinalCrossoverRouteTailRecordTokens decider symbols)

/-- Expand the compiled routed-clause and routed-variable input records. -/
def directSourceFinalRoutedBatchedRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  HorizontalRoutedRouteTailRecord.batchedRecords
    (directSourceFinalRoutedRouteTailRecordTokens decider symbols)

/-- The crossover and carrier prefix of the final copied-record stream. -/
def directSourceFinalCrossoverCarrierCompiledRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  directSourceFinalCrossoverBatchedRecords decider symbols ++
    directSourceFinalCarrierCompiledBatchedRecords decider symbols

/-- The bend, routed-clause, and routed-variable suffix. -/
def directSourceFinalBendRoutedCompiledRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  directSourceFinalBendCompiledBatchedRecords decider symbols ++
    directSourceFinalRoutedBatchedRecords decider symbols

/-- All five copied-clause families in their official final order. -/
def directSourceFinalFiveFamilyCompiledRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  directSourceFinalCrossoverCarrierCompiledRecords decider symbols ++
    directSourceFinalBendRoutedCompiledRecords decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
