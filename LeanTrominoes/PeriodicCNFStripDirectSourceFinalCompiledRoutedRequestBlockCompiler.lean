/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompiledRouteTailRecordSemantics
import LeanTrominoes.TM2CompositionMachine

/-! # Boundary-preserving final routed requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

namespace HorizontalRoutedRouteHeaderTailBlock

abbrev InputToken := HorizontalRoutedRouteHeaderTail.Token
abbrev RequestToken := HorizontalRoutedRouteDirectionRequest.Token

/-- A compact routed request token or the explicit end of that request.
Unlike `HorizontalRoutedRouteHeaderTail.output`, this alphabet retains one
boundary for every input record. -/
inductive Token
  | request (value : RequestToken)
  | requestEnd
  deriving DecidableEq, Fintype, Inhabited

def transition (active : Bool) : InputToken → Bool × List Token
  | .header header =>
      (HorizontalRoutedRouteHeaderTail.consumesTail header,
        (HorizontalRoutedRouteHeader.tokens header).map .request)
  | .tailDirection direction =>
      (active,
        if active then
          [.request (.tailDirection direction)]
        else [])
  | .recordEnd => (false, [.requestEnd])

def finish (_ : Bool) : List Token := []

/-- Complete every header/tail record while retaining its boundary. -/
def output (input : List InputToken) : List Token :=
  FiniteStateTransducer.output false transition finish input

/-- Canonical framed output of one completed routed request. -/
def requestBlock
    (header : HorizontalRoutedRouteHeaderTail.Header)
    (sourceTailDirections : List AxisDirection) : List Token :=
  (HorizontalRoutedRouteDirectionRequest.tokens
      (HorizontalRoutedRouteHeader.block
        header sourceTailDirections)).map .request ++
    [.requestEnd]

private theorem scan_tailRecord (active : Bool)
    (directions : List AxisDirection) :
    FiniteStateTransducer.scan transition active
        (directions.map
            HorizontalRoutedRouteHeaderTail.Token.tailDirection ++
          [.recordEnd]) =
      (false,
        (if active then
          directions.map fun direction =>
            Token.request (.tailDirection direction)
        else []) ++ [.requestEnd]) := by
  induction directions generalizing active with
  | nil => cases active <;> rfl
  | cons direction directions induction =>
      cases active <;>
        simp [FiniteStateTransducer.scan, transition, induction]

private theorem scan_record (active : Bool)
    (header : HorizontalRoutedRouteHeaderTail.Header)
    (sourceTailDirections : List AxisDirection) :
    FiniteStateTransducer.scan transition active
        (HorizontalRoutedRouteHeaderTail.record
          header sourceTailDirections) =
      (false, requestBlock header sourceTailDirections) := by
  rcases header with ⟨⟨sourceSlot, operation⟩, figurePrefix⟩
  cases figurePrefix <;> cases operation <;>
    simp [HorizontalRoutedRouteHeaderTail.record,
      FiniteStateTransducer.scan, transition,
      HorizontalRoutedRouteHeaderTail.consumesTail,
      scan_tailRecord, requestBlock,
      HorizontalRoutedRouteHeader.tokens,
      HorizontalRoutedRouteHeader.block,
      HorizontalRoutedRouteHeader.operationBlock,
      HorizontalRoutedRouteDirectionRequest.tokens,
      HorizontalRoutedRouteDirectionRequest.sourceTokens]

@[simp] theorem output_record
    (header : HorizontalRoutedRouteHeaderTail.Header)
    (sourceTailDirections : List AxisDirection) :
    output (HorizontalRoutedRouteHeaderTail.record
        header sourceTailDirections) =
      requestBlock header sourceTailDirections := by
  unfold output FiniteStateTransducer.output
  rw [scan_record]
  simp [finish]

theorem output_record_append
    (header : HorizontalRoutedRouteHeaderTail.Header)
    (sourceTailDirections : List AxisDirection)
    (remaining : List InputToken) :
    output (HorizontalRoutedRouteHeaderTail.record
        header sourceTailDirections ++ remaining) =
      requestBlock header sourceTailDirections ++ output remaining := by
  unfold output FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append, scan_record]
  simp [finish]

@[simp] theorem output_records
    (values : List
      (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection)) :
    output (HorizontalRoutedRouteHeaderTail.records values) =
      values.flatMap fun value => requestBlock value.1 value.2 := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      change output
          (HorizontalRoutedRouteHeaderTail.record value.1 value.2 ++
            HorizontalRoutedRouteHeaderTail.records values) = _
      rw [output_record_append, induction]
      rfl

/-- Boundary-preserving completion is a fixed finite-state linear-time pass. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime false transition finish

end HorizontalRoutedRouteHeaderTailBlock

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCompiledRoutedRequestBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Canonical boundary-preserving routed requests from the retained Figure 9
header/tail record stream. -/
def directFigureNinePolarityRoutedRequestBlockTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTailBlock.Token :=
  HorizontalRoutedRouteHeaderTailBlock.output
    (directFigureNinePolarityRouteTailRecords decider symbols)

/-- Compile the final direct header/tail records without erasing their
one-request boundaries. -/
def directSourceFinalCompiledRoutedRequestBlockTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTailBlock.Token :=
  HorizontalRoutedRouteHeaderTailBlock.output
    (directSourceFinalCompiledRouteTailRecords decider symbols)

/-- The complete boundary-preserving request stream is polynomial-time. -/
noncomputable def
    directSourceFinalCompiledRoutedRequestBlockTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCompiledRoutedRequestBlockTokens decider) := by
  unfold directSourceFinalCompiledRoutedRequestBlockTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCompiledRouteTailRecordsComputableInPolyTime decider)
    HorizontalRoutedRouteHeaderTailBlock.computableInPolyTime

/-- The compiled framed stream is exactly the canonical retained Figure 9
request stream, with one explicit end marker per occurrence. -/
@[simp] theorem directSourceFinalCompiledRoutedRequestBlockTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCompiledRoutedRequestBlockTokens decider symbols =
      directFigureNinePolarityRoutedRequestBlockTokens decider symbols := by
  unfold directSourceFinalCompiledRoutedRequestBlockTokens
    directFigureNinePolarityRoutedRequestBlockTokens
  rw [directSourceFinalCompiledRouteTailRecords_eq]

end LeanTrominoes.PeriodicCNFStripReduction

end
