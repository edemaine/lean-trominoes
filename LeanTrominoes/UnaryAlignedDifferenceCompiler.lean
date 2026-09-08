/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedWordPairCompiler

/-! # Pointwise signed differences of compiled unary columns -/

noncomputable section
namespace LeanTrominoes.UnaryAlignedDifference
open Computability Turing

/-- Positive or negative magnitude after cancelling aligned unary fields. -/
def values (keepPositive : Bool) (positive negative : List Nat) : List Nat :=
  DelimitedBinaryWordPairExcessMachine.excesses keepPositive
    (UnaryAlignedWordPairs.input positive negative)

noncomputable def nativeListComputableInPolyTime {Symbol : Type} [Fintype Symbol]
    (keepPositive : Bool) (positive negative : List Symbol → List Nat)
    (aligned : ∀ source, (positive source).length = (negative source).length)
    (positiveCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields positive)
    (negativeCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields negative) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun source => values keepPositive (positive source) (negative source)) :=
  TM2CompositionMachine.computableInPolyTime
    (UnaryAlignedWordPairs.inputComputableInPolyTime positive negative aligned
      positiveCompiler negativeCompiler)
    (DelimitedBinaryWordPairExcessMachine.computableInPolyTime keepPositive)

theorem values_eq_zipWith (keepPositive : Bool) (positive negative : List Nat) :
    values keepPositive positive negative =
      List.zipWith (fun first second => if keepPositive then first - second else second - first)
        positive negative := by
  induction positive generalizing negative with
  | nil => rfl
  | cons first positive induction =>
      cases negative with
      | nil => rfl
      | cons second negative =>
          simp only [values, UnaryAlignedWordPairs.input,
            DelimitedBinaryWordPairExcessMachine.excesses, List.zip_cons_cons,
            List.map_cons, List.zipWith_cons_cons] at induction ⊢
          rw [induction]
          simp [DelimitedBinaryWordPairExcessMachine.excess]

@[simp] theorem values_length (keepPositive : Bool) (positive negative : List Nat) :
    (values keepPositive positive negative).length = min positive.length negative.length := by
  rw [values_eq_zipWith, List.length_zipWith]

/-- Normalization preserves the common index order of two mapped columns. -/
theorem values_map {Index : Type} (indices : List Index) (keepPositive : Bool)
    (positive negative : Index → Nat) :
    values keepPositive (indices.map positive) (indices.map negative) =
      indices.map fun index =>
        let value : Int := (positive index : Int) - negative index
        if keepPositive then value.toNat else (-value).toNat := by
  rw [values_eq_zipWith]
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.map_cons, List.zipWith_cons_cons, induction]
      congr 1
      cases keepPositive <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

end LeanTrominoes.UnaryAlignedDifference
end
