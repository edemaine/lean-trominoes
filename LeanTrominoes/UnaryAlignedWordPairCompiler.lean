/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryBooleanChoiceSemantics
import LeanTrominoes.UnaryAlignedAddNativeListCompiler
import LeanTrominoes.DelimitedBinaryWordPairExcessTime
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime

/-! # Encoding aligned unary columns as length-coded word pairs -/

noncomputable section
namespace LeanTrominoes.UnaryAlignedWordPairs
open Computability Turing UnaryFieldEncoderMachine
open FiniteStateTransducer

inductive Control
  | start | first | second
  deriving DecidableEq, Fintype

def transition : Control → Symbol → Control × List DelimitedBinaryWordPairs.Token
  | .start, .unit => (.first, [.pairStart, .firstBit false])
  | .start, .delimiter => (.second, [.pairStart, .middle])
  | .first, .unit => (.first, [.firstBit false])
  | .first, .delimiter => (.second, [.middle])
  | .second, .unit => (.second, [.secondBit false])
  | .second, .delimiter => (.start, [.pairEnd])

def finish (_ : Control) : List DelimitedBinaryWordPairs.Token := []
def tokens := FiniteStateTransducer.output Control.start transition finish

def input (first second : List Nat) : DelimitedBinaryWordPairs.Input :=
  ⟨(first.zip second).map fun pair =>
    (List.replicate pair.1 false, List.replicate pair.2 false)⟩

private theorem scan_first (value : Nat) :
    scan transition .first (unaryField value) =
      (.second, List.replicate value (.firstBit false) ++ [.middle]) := by
  induction value with
  | zero => rfl
  | succ value induction =>
      rw [unaryField, List.replicate_succ, List.cons_append]
      simp only [scan, transition]
      rw [← unaryField, induction]
      rfl

private theorem scan_start (value : Nat) :
    scan transition .start (unaryField value) =
      (.second, .pairStart :: (List.replicate value (.firstBit false) ++ [.middle])) := by
  cases value with
  | zero => rfl
  | succ value =>
      rw [unaryField, List.replicate_succ, List.cons_append]
      simp only [scan, transition]
      rw [← unaryField, scan_first]
      rfl

private theorem scan_second (value : Nat) :
    scan transition .second (unaryField value) =
      (.start, List.replicate value (.secondBit false) ++ [.pairEnd]) := by
  induction value with
  | zero => rfl
  | succ value induction =>
      rw [unaryField, List.replicate_succ, List.cons_append]
      simp only [scan, transition]
      rw [← unaryField, induction]
      rfl

private theorem scan_interleaved (first second : List Nat) :
    scan transition .start
        (unaryFields (AlignedUnaryBooleanChoice.interleaved first second)) =
      (.start, DelimitedBinaryWordPairs.encode (input first second)) := by
  induction first generalizing second with
  | nil => rfl
  | cons first firsts induction =>
      cases second with
      | nil => rfl
      | cons second seconds =>
          simp only [AlignedUnaryBooleanChoice.interleaved, unaryFields_cons,
            scan_append, scan_start, scan_second]
          rw [induction]
          simp [input, DelimitedBinaryWordPairs.encode, DelimitedBinaryWordPairs.pairTokens,
            List.map_replicate, List.append_assoc]

theorem tokens_interleaved (first second : List Nat) :
    tokens (unaryFields (AlignedUnaryBooleanChoice.interleaved first second)) =
      DelimitedBinaryWordPairs.encode (input first second) := by
  unfold tokens FiniteStateTransducer.output
  rw [scan_interleaved]
  simp [finish]

/-- Align two native-input column compilers and encode their entries as pairs
of unary-length words, without converting binary values to unary. -/
noncomputable def inputComputableInPolyTime {InputSymbol : Type} [Fintype InputSymbol]
    (first second : List InputSymbol → List Nat)
    (aligned : ∀ source, (first source).length = (second source).length)
    (firstCompiler : TM2ComputableInPolyTime id unaryFields first)
    (secondCompiler : TM2ComputableInPolyTime id unaryFields second) :
    TM2ComputableInPolyTime id DelimitedBinaryWordPairs.encode
      (fun source => input (first source) (second source)) := by
  let interleavedCompiler := UnaryAlignedAddMachine.nativeListComputableInPolyTime
    (fun source => UnaryFieldAlternatingPadding.appendZeroValues (first source))
    (fun source => UnaryFieldAlternatingPadding.prependZeroValues (second source))
    (fun source => by simp [aligned source])
    (TM2CompositionMachine.computableInPolyTime firstCompiler
      UnaryFieldAlternatingPadding.appendZeroValuesComputableInPolyTime)
    (TM2CompositionMachine.computableInPolyTime secondCompiler
      UnaryFieldAlternatingPadding.prependZeroValuesComputableInPolyTime)
  let encoded : TM2ComputableInPolyTime unaryFields id
      (fun values => tokens (unaryFields values)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
      (FiniteStateTransducer.computableInPolyTime Control.start transition finish)
      (fun _ => rfl) (fun _ => rfl)
  let composed := TM2CompositionMachine.computableInPolyTime interleavedCompiler encoded
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
  intro source
  change tokens (unaryFields (AlignedUnaryBooleanChoice.candidateValues
    (first source) (second source))) = _
  rw [AlignedUnaryBooleanChoice.candidateValues_eq_interleaved, tokens_interleaved]

end LeanTrominoes.UnaryAlignedWordPairs
end
