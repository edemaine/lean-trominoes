/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenCounts
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenSourceSemantics
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time unary source clause counts -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.SourceClauseCountField

open Computability Turing

def transition (_ : Unit) (token : SourceOccurrenceRouteTokens.Token) :
    Unit × List UnaryFieldEncoderMachine.Symbol :=
  ((), if SourceOccurrenceRouteTokens.isClause token then
    [.unit] else [])

def finish (_ : Unit) : List UnaryFieldEncoderMachine.Symbol :=
  [.delimiter]

def ofTokens (tokens : List SourceOccurrenceRouteTokens.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  FiniteStateTransducer.output () transition finish tokens

theorem scan_eq (tokens : List SourceOccurrenceRouteTokens.Token) :
    FiniteStateTransducer.scan transition () tokens =
      ((), List.replicate
        (UnaryPolynomialPaddingMachine.selectedCount
          SourceOccurrenceRouteTokens.isClause tokens) .unit) := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      cases token <;>
        simp [FiniteStateTransducer.scan, transition,
          SourceOccurrenceRouteTokens.isClause,
          UnaryPolynomialPaddingMachine.selectedCount, induction,
          List.replicate_add]

theorem ofTokens_eq_unaryField
    (tokens : List SourceOccurrenceRouteTokens.Token) :
    ofTokens tokens =
      UnaryFieldEncoderMachine.unaryField
        (UnaryPolynomialPaddingMachine.selectedCount
          SourceOccurrenceRouteTokens.isClause tokens) := by
  simp [ofTokens, FiniteStateTransducer.output, scan_eq, finish,
    UnaryFieldEncoderMachine.unaryField]

def sourceField (source : SourceSplitRouteDescriptorTokens.Source) :
    List UnaryFieldEncoderMachine.Symbol :=
  ofTokens (SourceOccurrenceRouteTokens.sourceTokens source)

theorem sourceField_eq (source :
    SourceSplitRouteDescriptorTokens.Source) :
    sourceField source =
      UnaryFieldEncoderMachine.unaryField source.formula.clauses.length := by
  rw [sourceField, ofTokens_eq_unaryField,
    SourceOccurrenceRouteTokens.sourceTokens_eq_formulaTokens,
    SourceOccurrenceRouteTokens.selectedCount_isClause_formulaTokens]

/-- The exact source clause count is emitted as one unary field in
polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode id sourceField := by
  let counter := FiniteStateTransducer.computableInPolyTime
    () transition finish
  change TM2ComputableInPolyTime
    SourceSplitRouteDescriptorTokens.finEncoding.encode id
    (fun source => FiniteStateTransducer.output () transition finish
      (SourceOccurrenceRouteTokens.sourceTokens source))
  exact TM2CompositionMachine.computableInPolyTime
    SourceOccurrenceRouteTokens.sourceTokensComputableInPolyTime counter

end LeanTrominoes.PeriodicCNF.SourceClauseCountField

end
