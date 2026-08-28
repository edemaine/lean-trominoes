/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanRouteTailRecordDecoder
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanTerminalColumnData
import LeanTrominoes.TM2BooleanClosure
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for packed carrier terminal-direction columns -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierPackedSpanTerminalColumns

open Computability Turing
open CarrierPackedSpanRouteTailRecords

def hasUnitTransition : Bool → Symbol → Bool × List Bool
  | false, .unit => (true, [true])
  | false, .delimiter => (true, [false])
  | true, _ => (true, [])

def hasUnitFinish : Bool → List Bool
  | false => [false]
  | true => []

def hasUnitWords (block : List Symbol) : List Bool :=
  FiniteStateTransducer.output false
    hasUnitTransition hasUnitFinish block

@[simp] theorem hasUnitScan_done (block : List Symbol) :
    FiniteStateTransducer.scan hasUnitTransition true block =
      (true, []) := by
  induction block with
  | nil => rfl
  | cons symbol block induction =>
      cases symbol <;>
        simp [FiniteStateTransducer.scan, hasUnitTransition, induction]

@[simp] theorem hasUnitWords_eq (block : List Symbol) :
    hasUnitWords block = [hasUnit block] := by
  cases block with
  | nil => rfl
  | cons symbol block =>
      cases symbol <;>
        simp [hasUnitWords, FiniteStateTransducer.output,
          FiniteStateTransducer.scan, hasUnitTransition,
          hasUnitFinish, hasUnit]

noncomputable def hasUnitComputableInPolyTime :
    TM2ComputableInPolyTime id TM2BooleanClosure.booleanEncoding
      hasUnit := by
  let physical : TM2ComputableInPolyTime id id hasUnitWords :=
    FiniteStateTransducer.computableInPolyTime
      false hasUnitTransition hasUnitFinish
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    physical hasUnitWords_eq

def fixedWordTransition : Unit → Symbol → Unit × List Symbol :=
  fun _ _ => ((), [])

def fixedWordFinish (word : List Symbol) : Unit → List Symbol :=
  fun _ => word

def fixedWords (word : List Symbol) (block : List Symbol) : List Symbol :=
  FiniteStateTransducer.output () fixedWordTransition
    (fixedWordFinish word) block

@[simp] theorem fixedWordScan (block : List Symbol) :
    FiniteStateTransducer.scan fixedWordTransition () block = ((), []) := by
  induction block with
  | nil => rfl
  | cons symbol block induction =>
      simp [FiniteStateTransducer.scan, fixedWordTransition, induction]

@[simp] theorem fixedWords_eq (word block : List Symbol) :
    fixedWords word block = word := by
  simp [fixedWords, FiniteStateTransducer.output, fixedWordFinish]

noncomputable def fixedWordComputableInPolyTime (word : List Symbol) :
    TM2ComputableInPolyTime id id
      (fun _ : List Symbol => word) := by
  let physical : TM2ComputableInPolyTime id id (fixedWords word) :=
    FiniteStateTransducer.computableInPolyTime
      () fixedWordTransition (fixedWordFinish word)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    physical (fixedWords_eq word)

noncomputable def activeResidueComputableInPolyTime
    (residue : Residue) :
    TM2ComputableInPolyTime id TM2BooleanClosure.booleanEncoding
      (fun block => hasUnit block && hasResidue residue block) :=
  TM2BooleanClosure.forkComputableInPolyTime
    hasUnitComputableInPolyTime
    (hasResidueComputableInPolyTime residue) (fun first second =>
      first && second)

noncomputable def guardedDirectionCandidateComputableInPolyTime
    (residue : Residue) (horizontal : Bool) :
    TM2ComputableInPolyTime id id
      (guardedDirectionCandidate residue horizontal) := by
  change TM2ComputableInPolyTime id id (fun block =>
    SeparatedBooleanGuard.guarded
      (hasUnit block && hasResidue residue block,
        UnaryFieldEncoderMachine.unaryFields
          (directionRankValues horizontal)))
  let paired := TM2ForkMachine.computableInPolyTime
    (activeResidueComputableInPolyTime residue)
    (fixedWordComputableInPolyTime
      (UnaryFieldEncoderMachine.unaryFields
        (directionRankValues horizontal)))
  exact TM2CompositionMachine.computableInPolyTime paired
    (SeparatedBooleanGuard.computableInPolyTime (Symbol := Symbol))

noncomputable def directionRankBlockOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id directionRankBlockOutput := by
  exact TM2ListAppend.computableInPolyTime
    (TM2ListAppend.computableInPolyTime
      (TM2ListAppend.computableInPolyTime
        (guardedDirectionCandidateComputableInPolyTime .zero false)
        (guardedDirectionCandidateComputableInPolyTime .one false))
      (guardedDirectionCandidateComputableInPolyTime .two true))
    (guardedDirectionCandidateComputableInPolyTime .three true)

noncomputable def directionRankStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id directionRankStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    directionRankBlockOutputComputableInPolyTime
    CarrierSpanRouteDirections.isFieldEnd

end CarrierPackedSpanTerminalColumns
end LeanTrominoes.PeriodicOrthocrossing

end
