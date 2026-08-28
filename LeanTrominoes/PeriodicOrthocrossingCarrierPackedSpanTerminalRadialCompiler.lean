/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanTerminalDirectionCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for packed carrier terminal-radial columns -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierPackedSpanTerminalColumns

open Computability Turing
open CarrierPackedSpanRouteTailRecords

/-- Nine states count the first eight discarded symbols. -/
abbrev DropEightControl := Fin 9

def dropEightTransition : DropEightControl → Symbol →
    DropEightControl × List Symbol
  | control, symbol =>
      if h : control.val < 8 then
        (⟨control.val + 1, Nat.succ_lt_succ h⟩, [])
      else
        (control, [symbol])

def dropEightFinish (_ : DropEightControl) : List Symbol := []

def dropEightOutput (word : List Symbol) : List Symbol :=
  FiniteStateTransducer.output (0 : DropEightControl)
    dropEightTransition dropEightFinish word

@[simp] theorem dropEightScan_eight (word : List Symbol) :
    FiniteStateTransducer.scan dropEightTransition
        (8 : DropEightControl) word =
      ((8 : DropEightControl), word) := by
  induction word with
  | nil => rfl
  | cons symbol word induction =>
      simp [FiniteStateTransducer.scan, dropEightTransition, induction]

/-- The finite-state counter implements ordinary eight-symbol deletion. -/
theorem dropEightOutput_eq_drop (word : List Symbol) :
    dropEightOutput word = word.drop 8 := by
  cases word with
  | nil => rfl
  | cons first word =>
    cases word with
    | nil => rfl
    | cons second word =>
      cases word with
      | nil => rfl
      | cons third word =>
        cases word with
        | nil => rfl
        | cons fourth word =>
          cases word with
          | nil => rfl
          | cons fifth word =>
            cases word with
            | nil => rfl
            | cons sixth word =>
              cases word with
              | nil => rfl
              | cons seventh word =>
                cases word with
                | nil => rfl
                | cons eighth word =>
                  simp [dropEightOutput,
                    FiniteStateTransducer.output,
                    FiniteStateTransducer.scan,
                    dropEightTransition, dropEightFinish]

noncomputable def dropEightOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id dropEightOutput := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output (0 : DropEightControl)
      dropEightTransition dropEightFinish)
  exact FiniteStateTransducer.computableInPolyTime
    (0 : DropEightControl) dropEightTransition dropEightFinish

def radialLengthCandidateComputed (block : List Symbol) : List Symbol :=
  UnaryFieldEncoderMachine.unaryFields [3, 2, 1] ++
    dropEightOutput (reducedOutput block)

theorem radialLengthCandidateComputed_eq
    (block : List Symbol) :
    radialLengthCandidateComputed block = radialLengthCandidate block := by
  unfold radialLengthCandidateComputed radialLengthCandidate
  rw [dropEightOutput_eq_drop]

noncomputable def radialLengthCandidateComputedComputableInPolyTime :
    TM2ComputableInPolyTime id id radialLengthCandidateComputed := by
  let dropped := TM2CompositionMachine.computableInPolyTime
    reducedOutputComputableInPolyTime
    dropEightOutputComputableInPolyTime
  exact TM2ListAppend.computableInPolyTime
    (fixedWordComputableInPolyTime
      (UnaryFieldEncoderMachine.unaryFields [3, 2, 1]))
    dropped

noncomputable def radialLengthCandidateComputableInPolyTime :
    TM2ComputableInPolyTime id id radialLengthCandidate :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    radialLengthCandidateComputedComputableInPolyTime
    radialLengthCandidateComputed_eq

noncomputable def radialLengthBlockOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id radialLengthBlockOutput := by
  change TM2ComputableInPolyTime id id (fun block =>
    SeparatedBooleanGuard.guarded
      (hasUnit block, radialLengthCandidate block))
  let paired := TM2ForkMachine.computableInPolyTime
    hasUnitComputableInPolyTime
    radialLengthCandidateComputableInPolyTime
  exact TM2CompositionMachine.computableInPolyTime paired
    (SeparatedBooleanGuard.computableInPolyTime (Symbol := Symbol))

noncomputable def radialLengthStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id radialLengthStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    radialLengthBlockOutputComputableInPolyTime
    CarrierSpanRouteDirections.isFieldEnd

end CarrierPackedSpanTerminalColumns
end LeanTrominoes.PeriodicOrthocrossing

end
