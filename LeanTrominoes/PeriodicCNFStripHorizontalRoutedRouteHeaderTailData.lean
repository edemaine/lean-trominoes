/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderData

/-! # Streaming dynamic tails into finite routed headers -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderTail

open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix

abbrev Header :=
  PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header

abbrev RequestToken := HorizontalRoutedRouteDirectionRequest.Token

/-- One finite header followed by its possibly dynamic source-tail word.
The explicit end marker prevents a malformed local record from leaking tail
directions into the next inherited record. -/
inductive Token
  | header (value : Header)
  | tailDirection (value : AxisDirection)
  | recordEnd
  deriving DecidableEq, Fintype, Inhabited

/-- Whether the current header genuinely consumes dynamic tail directions. -/
def consumesTail (header : Header) : Bool :=
  match header.figurePrefix with
  | .local _ => false
  | .inherited _ _ => true

/-- Finite control remembers only whether tail directions should pass through. -/
def transition (active : Bool) : Token → Bool × List RequestToken
  | .header header =>
      (consumesTail header, HorizontalRoutedRouteHeader.tokens header)
  | .tailDirection direction =>
      (active, if active then [.tailDirection direction] else [])
  | .recordEnd => (false, [])

def finish (_ : Bool) : List RequestToken := []

/-- Complete every finite header by streaming through precisely the dynamic
tail directions consumed by inherited Figure 9 routes. -/
def output (input : List Token) : List RequestToken :=
  FiniteStateTransducer.output false transition finish input

/-- Canonical record for one header and its aligned source-tail word. -/
def record (header : Header) (sourceTailDirections : List AxisDirection) :
    List Token :=
  .header header ::
    sourceTailDirections.map .tailDirection ++ [.recordEnd]

private theorem scan_tailDirections (active : Bool)
    (directions : List AxisDirection) :
    FiniteStateTransducer.scan transition active
        (directions.map Token.tailDirection) =
      (active,
        if active then
          directions.map
            HorizontalRoutedRouteDirectionRequest.Token.tailDirection
        else []) := by
  induction directions with
  | nil => cases active <;> rfl
  | cons direction directions induction =>
      cases active <;>
        simp [FiniteStateTransducer.scan, transition, induction]

private theorem scan_tailRecord (active : Bool)
    (directions : List AxisDirection) :
    FiniteStateTransducer.scan transition active
        (directions.map Token.tailDirection ++ [.recordEnd]) =
      (false,
        if active then
          directions.map
            HorizontalRoutedRouteDirectionRequest.Token.tailDirection
        else []) := by
  induction directions generalizing active with
  | nil =>
      cases active <;>
        simp [FiniteStateTransducer.scan, transition]
  | cons direction directions induction =>
      cases active <;>
        simp [FiniteStateTransducer.scan, transition, induction]

private theorem scan_record (active : Bool) (header : Header)
    (sourceTailDirections : List AxisDirection) :
    FiniteStateTransducer.scan transition active
        (record header sourceTailDirections) =
      (false,
        HorizontalRoutedRouteDirectionRequest.tokens
          (HorizontalRoutedRouteHeader.block
            header sourceTailDirections)) := by
  rcases header with ⟨⟨sourceSlot, operation⟩, figurePrefix⟩
  cases figurePrefix <;> cases operation <;>
    simp [record, FiniteStateTransducer.scan, transition, consumesTail,
      scan_tailRecord, HorizontalRoutedRouteHeader.tokens,
      HorizontalRoutedRouteHeader.block,
      HorizontalRoutedRouteHeader.operationBlock,
      HorizontalRoutedRouteDirectionRequest.tokens,
      HorizontalRoutedRouteDirectionRequest.sourceTokens]

/-- A canonical record becomes exactly the established compact request for
the completed routed block.  In particular, local headers ignore any
malformed supplied tail, while inherited headers pass the whole tail. -/
@[simp] theorem output_record (header : Header)
    (sourceTailDirections : List AxisDirection) :
    output (record header sourceTailDirections) =
      HorizontalRoutedRouteDirectionRequest.tokens
        (HorizontalRoutedRouteHeader.block
          header sourceTailDirections) := by
  unfold output FiniteStateTransducer.output
  rw [scan_record]
  simp [finish]

/-- A complete record resets finite control before processing any following
stream. -/
theorem output_record_append (header : Header)
    (sourceTailDirections : List AxisDirection) (remaining : List Token) :
    output (record header sourceTailDirections ++ remaining) =
      HorizontalRoutedRouteDirectionRequest.tokens
          (HorizontalRoutedRouteHeader.block
            header sourceTailDirections) ++
        output remaining := by
  unfold output FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append, scan_record]
  simp [finish]

/-- Serialize a list of aligned header/tail pairs as complete records. -/
def records (values : List (Header × List AxisDirection)) : List Token :=
  values.flatMap fun value => record value.1 value.2

/-- Record streaming independently completes every aligned header/tail pair
in presentation order. -/
@[simp] theorem output_records
    (values : List (Header × List AxisDirection)) :
    output (records values) =
      values.flatMap fun value =>
        HorizontalRoutedRouteDirectionRequest.tokens
          (HorizontalRoutedRouteHeader.block value.1 value.2) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      change output (record value.1 value.2 ++ records values) = _
      rw [output_record_append, induction]
      rfl

end HorizontalRoutedRouteHeaderTail
end PeriodicCNFStripReduction
end LeanTrominoes
