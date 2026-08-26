/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessTime
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.SignedUnarySuccessorData
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for successor matrices over signed unary values -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace UnaryFieldSuccessorRows

/-- Exact-one row-major truncated differences are polynomial-time computable
from any compiled unary field column. -/
noncomputable def bitsComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (values : Input → List Nat)
    (valuesCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields values)
    (keepFirst : Bool) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => bits keepFirst (values input)) := by
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    valuesCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  let pairCompilerRaw := TM2CompositionMachine.computableInPolyTime
    wordCompiler DelimitedBinaryWordPairProductMachine.computableInPolyTime
  let pairCompiler : TM2ComputableInPolyTime encodeInput
      DelimitedBinaryWordPairs.finEncoding.encode
      (fun input => wordPairs (values input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      pairCompilerRaw (fun _ => rfl)
  let excessCompilerRaw := TM2CompositionMachine.computableInPolyTime
    pairCompiler
    (DelimitedBinaryWordPairExcessMachine.computableInPolyTime keepFirst)
  let excessCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields
      (fun input => excesses keepFirst (values input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      excessCompilerRaw (fun _ => rfl)
  let composed := TM2CompositionMachine.computableInPolyTime
    excessCompiler UnaryExactOneBooleans.bitsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    composed (fun _ => rfl)

end UnaryFieldSuccessorRows

namespace SignedUnarySuccessor

open SignedUnaryStrictLower

noncomputable def bothZeroBitsComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (values : Input → List Nat)
    (valuesCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields values) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => bothZeroBits (values input)) := by
  let firstPresentCompiler :=
    UnaryFieldPairPresence.fieldBitsComputableInPolyTime
      encodeInput values valuesCompiler .first
  let secondPresentCompiler :=
    UnaryFieldPairPresence.fieldBitsComputableInPolyTime
      encodeInput values valuesCompiler .second
  let firstZeroCompiler :=
    AlignedBooleanListClosure.mapNegatedComputableInPolyTime
      encodeInput
      (fun input => UnaryFieldPairPresence.fieldBits .first (values input))
      firstPresentCompiler
  let secondZeroCompiler :=
    AlignedBooleanListClosure.mapNegatedComputableInPolyTime
      encodeInput
      (fun input => UnaryFieldPairPresence.fieldBits .second (values input))
      secondPresentCompiler
  exact AlignedBooleanListClosure.combinedComputableInPolyTime
    encodeInput .conjunction
    (fun input => AlignedBooleanListClosure.negated
      (UnaryFieldPairPresence.fieldBits .first (values input)))
    (fun input => AlignedBooleanListClosure.negated
      (UnaryFieldPairPresence.fieldBits .second (values input)))
    (fun input => by simp)
    firstZeroCompiler secondZeroCompiler

/-- Signed-unary successor matrices are polynomial-time computable from
aligned positive and negative magnitude columns. -/
noncomputable def bitsComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (positive negative : Input → List Nat)
    (lengthEq : ∀ input,
      (positive input).length = (negative input).length)
    (positiveCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields positive)
    (negativeCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields negative) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => bits (positive input) (negative input)) := by
  let positiveSuccessorCompiler :=
    UnaryFieldSuccessorRows.bitsComputableInPolyTime
      encodeInput positive positiveCompiler false
  let negativePredecessorCompiler :=
    UnaryFieldSuccessorRows.bitsComputableInPolyTime
      encodeInput negative negativeCompiler true
  let negativeZeroCompiler := bothZeroBitsComputableInPolyTime
    encodeInput negative negativeCompiler
  let positiveZeroCompiler := bothZeroBitsComputableInPolyTime
    encodeInput positive positiveCompiler
  let nonnegativeCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      encodeInput .conjunction
      (fun input => UnaryFieldSuccessorRows.bits false (positive input))
      (fun input => bothZeroBits (negative input))
      (fun input => by simp [lengthEq input])
      positiveSuccessorCompiler negativeZeroCompiler
  let negativeCaseCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      encodeInput .conjunction
      (fun input => UnaryFieldSuccessorRows.bits true (negative input))
      (fun input => bothZeroBits (positive input))
      (fun input => by simp [lengthEq input])
      negativePredecessorCompiler positiveZeroCompiler
  exact AlignedBooleanListClosure.combinedComputableInPolyTime
    encodeInput .disjunction
    (fun input => nonnegativeCase (positive input) (negative input))
    (fun input => negativeCase (positive input) (negative input))
    (fun input => by simp [lengthEq input])
    nonnegativeCompiler negativeCaseCompiler

end SignedUnarySuccessor
end LeanTrominoes

end
