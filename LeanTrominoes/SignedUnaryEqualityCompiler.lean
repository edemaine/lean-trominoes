/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedBooleanListClosure
import LeanTrominoes.UnaryFieldEqualityRowsCompiler

/-! # Equality matrices for signed unary fields -/

noncomputable section

namespace LeanTrominoes
namespace SignedUnaryEquality

open Computability Turing

def equalityBits (positive negative : List Nat) : List Bool :=
  List.zipWith (· && ·)
    (UnaryFieldEqualityRows.equalityBits positive)
    (UnaryFieldEqualityRows.equalityBits negative)

@[simp] theorem equalityBits_length
    {positive negative : List Nat}
    (lengthEq : positive.length = negative.length) :
    (equalityBits positive negative).length = positive.length ^ 2 := by
  simp [equalityBits, lengthEq]

/-- Equality of aligned canonical positive/negative unary magnitudes is
computable in polynomial time. -/
noncomputable def equalityBitsComputableInPolyTime
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
      (fun input => equalityBits
        (positive input) (negative input)) :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    encodeInput .conjunction
    (fun input => UnaryFieldEqualityRows.equalityBits (positive input))
    (fun input => UnaryFieldEqualityRows.equalityBits (negative input))
    (fun input => by simp [lengthEq input])
    (UnaryFieldEqualityRows.equalityBitsComputableInPolyTime
      encodeInput positive positiveCompiler)
    (UnaryFieldEqualityRows.equalityBitsComputableInPolyTime
      encodeInput negative negativeCompiler)

end SignedUnaryEquality
end LeanTrominoes

end
