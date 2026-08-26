/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedBooleanListClosure

/-! # Exact-one tests for unary fields -/

noncomputable section

namespace LeanTrominoes
namespace UnaryExactOneBooleans

open Computability Turing

/-- A unary field is exactly one precisely when it is nonempty but does not
contain the two units needed to make a conjunction true. -/
def bits (values : List Nat) : List Bool :=
  List.zipWith (fun positive notMany => positive && notMany)
    (UnarySmallSumBooleans.bits .disjunction values)
    (AlignedBooleanListClosure.negated
      (UnarySmallSumBooleans.bits .conjunction values))

private theorem exactOneValue (value : Nat) :
    (UnarySmallSumBooleans.sumBit .disjunction value &&
        !UnarySmallSumBooleans.sumBit .conjunction value) =
      decide (value = 1) := by
  cases value with
  | zero => rfl
  | succ value =>
      cases value with
      | zero => rfl
      | succ value => rfl

theorem bits_eq_map (values : List Nat) :
    bits values = values.map fun value => decide (value = 1) := by
  unfold bits UnarySmallSumBooleans.bits
    AlignedBooleanListClosure.negated
  rw [List.map_map]
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.map_cons, List.zipWith_cons_cons, induction]
      congr 1
      simpa only [Function.comp_apply] using exactOneValue value

@[simp] theorem bits_length (values : List Nat) :
    (bits values).length = values.length := by
  rw [bits_eq_map]
  simp

/-- Exact-one testing of delimiter-separated unary fields is polynomial-time
computable using the existing nonempty and at-least-two transducers. -/
noncomputable def bitsComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id bits := by
  let positiveCompiler :=
    UnarySmallSumBooleans.bitsComputableInPolyTime
      UnarySmallSumBooleans.Operation.disjunction
  let notManyCompiler :=
    AlignedBooleanListClosure.mapNegatedComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      (UnarySmallSumBooleans.bits
        UnarySmallSumBooleans.Operation.conjunction)
      (UnarySmallSumBooleans.bitsComputableInPolyTime
        UnarySmallSumBooleans.Operation.conjunction)
  exact AlignedBooleanListClosure.combinedComputableInPolyTime
    UnaryFieldEncoderMachine.unaryFields
    UnarySmallSumBooleans.Operation.conjunction
    (UnarySmallSumBooleans.bits
      UnarySmallSumBooleans.Operation.disjunction)
    (fun values => AlignedBooleanListClosure.negated
      (UnarySmallSumBooleans.bits
        UnarySmallSumBooleans.Operation.conjunction values))
    (fun values => by simp [UnarySmallSumBooleans.bits])
    positiveCompiler notManyCompiler

end UnaryExactOneBooleans
end LeanTrominoes

end
