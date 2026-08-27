/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingCarrierSpanRouteDirectionDecoder
import LeanTrominoes.PeriodicOrthocrossingCarrierTaggedSpanRouteDirectionDecoderData
import LeanTrominoes.SeparatedBooleanGuardCompiler
import LeanTrominoes.TM2BooleanClosure
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for parity-tagged retained carrier spans -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierTaggedSpanRouteDirections

open Computability Turing
open CarrierSpanRouteDirections

private def AxisControl.outputLength : AxisControl → Nat
  | .even | .odd => 1
  | .done => 0

private theorem axis_output_cons (control : AxisControl)
    (symbol : SourceSymbol) (block : List SourceSymbol) :
    FiniteStateTransducer.output control axisTransition axisFinish
        (symbol :: block) =
      (axisTransition control symbol).2 ++
        FiniteStateTransducer.output
          (axisTransition control symbol).1
          axisTransition axisFinish block := by
  unfold FiniteStateTransducer.output
  simp only [FiniteStateTransducer.scan]
  rw [List.append_assoc]

private theorem axisOutput_length_from (control : AxisControl) :
    ∀ block : List SourceSymbol,
      (FiniteStateTransducer.output control
        axisTransition axisFinish block).length = control.outputLength
  | [] => by cases control <;> rfl
  | symbol :: block => by
      rw [axis_output_cons]
      cases control <;> cases symbol <;>
        simp [axisTransition, AxisControl.outputLength,
          axisOutput_length_from]

theorem axisOutput_eq_singleton (block : List SourceSymbol) :
    axisOutput block = [isHorizontal block] := by
  have lengthEq : (axisOutput block).length = 1 := by
    exact axisOutput_length_from .even block
  unfold isHorizontal
  cases outputEq : axisOutput block with
  | nil => simp [outputEq] at lengthEq
  | cons axis remaining =>
      cases remaining with
      | nil => rfl
      | cons other remaining => simp [outputEq] at lengthEq

noncomputable def reducedOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id reducedOutput :=
  FiniteStateTransducer.computableInPolyTime
    ReductionControl.zero reducedTransition reducedFinish

private noncomputable def axisOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id axisOutput :=
  FiniteStateTransducer.computableInPolyTime
    AxisControl.even axisTransition axisFinish

noncomputable def isHorizontalComputableInPolyTime :
    TM2ComputableInPolyTime id TM2BooleanClosure.booleanEncoding
      isHorizontal :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    axisOutputComputableInPolyTime axisOutput_eq_singleton

noncomputable def horizontalCandidateComputableInPolyTime :
    TM2ComputableInPolyTime id id horizontalCandidate :=
  by
    change TM2ComputableInPolyTime id id
      (fun block => CarrierSpanRouteDirections.blockOutput true
        (reducedOutput block))
    exact TM2CompositionMachine.computableInPolyTime
      reducedOutputComputableInPolyTime
      (CarrierSpanRouteDirections.blockOutputComputableInPolyTime true)

noncomputable def verticalCandidateComputableInPolyTime :
    TM2ComputableInPolyTime id id verticalCandidate :=
  by
    change TM2ComputableInPolyTime id id
      (fun block => CarrierSpanRouteDirections.blockOutput false
        (reducedOutput block))
    exact TM2CompositionMachine.computableInPolyTime
      reducedOutputComputableInPolyTime
      (CarrierSpanRouteDirections.blockOutputComputableInPolyTime false)

private noncomputable def guardedCandidateComputableInPolyTime
    (active : List SourceSymbol → Bool)
    (candidate : List SourceSymbol → List Token)
    (activeCompiler :
      TM2ComputableInPolyTime id TM2BooleanClosure.booleanEncoding active)
    (candidateCompiler : TM2ComputableInPolyTime id id candidate) :
    TM2ComputableInPolyTime id id
      (fun block => SeparatedBooleanGuard.guarded
        (active block, candidate block)) := by
  let paired := TM2ForkMachine.computableInPolyTime
    activeCompiler candidateCompiler
  exact TM2CompositionMachine.computableInPolyTime paired
    (SeparatedBooleanGuard.computableInPolyTime (Symbol := Token))

private noncomputable def horizontalGuardedComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun block => SeparatedBooleanGuard.guarded
        (isHorizontal block, horizontalCandidate block)) :=
  guardedCandidateComputableInPolyTime
    isHorizontal horizontalCandidate
    isHorizontalComputableInPolyTime
    horizontalCandidateComputableInPolyTime

private noncomputable def verticalGuardedComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun block => SeparatedBooleanGuard.guarded
        (!isHorizontal block, verticalCandidate block)) :=
  guardedCandidateComputableInPolyTime
    (fun block => !isHorizontal block) verticalCandidate
    (TM2BooleanClosure.mapComputableInPolyTime
      isHorizontalComputableInPolyTime (!·))
    verticalCandidateComputableInPolyTime

noncomputable def blockOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id blockOutput :=
  TM2ListAppend.computableInPolyTime
    horizontalGuardedComputableInPolyTime
    verticalGuardedComputableInPolyTime

noncomputable def streamComputableInPolyTime :
    TM2ComputableInPolyTime id id stream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    blockOutputComputableInPolyTime
    CarrierSpanRouteDirections.isFieldEnd

end CarrierTaggedSpanRouteDirections
end LeanTrominoes.PeriodicOrthocrossing

end
