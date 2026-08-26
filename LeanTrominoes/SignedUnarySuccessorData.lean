/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessMachine
import LeanTrominoes.DelimitedBinaryWordPairProductMachine
import LeanTrominoes.SignedUnaryStrictLowerCompiler
import LeanTrominoes.UnaryExactOneBooleanCompiler
import LeanTrominoes.UnaryFieldBinaryWordCompiler

/-! # Successor matrices over signed unary values -/

namespace LeanTrominoes

namespace UnaryFieldSuccessorRows

def wordPairs (values : List Nat) : DelimitedBinaryWordPairs.Input :=
  DelimitedBinaryWordPairProductMachine.pairs
    (UnaryFieldBinaryWords.words values)

def excesses (keepFirst : Bool) (values : List Nat) : List Nat :=
  DelimitedBinaryWordPairExcessMachine.excesses keepFirst
    (wordPairs values)

/-- Row-major exact-one truncated differences.  `keepFirst = false` tests
`second = first + 1`; `true` tests `first = second + 1`. -/
def bits (keepFirst : Bool) (values : List Nat) : List Bool :=
  UnaryExactOneBooleans.bits (excesses keepFirst values)

private theorem orderedProduct_length {Value : Type*}
    (values : List Value) :
    (values.flatMap fun first =>
      values.map fun second => (first, second)).length = values.length ^ 2 := by
  simp [pow_two]

@[simp] theorem bits_length (keepFirst : Bool) (values : List Nat) :
    (bits keepFirst values).length = values.length ^ 2 := by
  unfold bits excesses wordPairs
  rw [UnaryExactOneBooleans.bits_length]
  rw [show
    (DelimitedBinaryWordPairExcessMachine.excesses keepFirst
      (DelimitedBinaryWordPairProductMachine.pairs
        (UnaryFieldBinaryWords.words values))).length =
      (DelimitedBinaryWordPairProductMachine.pairs
        (UnaryFieldBinaryWords.words values)).pairs.length
    by simp [DelimitedBinaryWordPairExcessMachine.excesses]]
  unfold DelimitedBinaryWordPairProductMachine.pairs
  rw [orderedProduct_length]
  simp [UnaryFieldBinaryWords.words]

end UnaryFieldSuccessorRows

namespace SignedUnarySuccessor

open SignedUnaryStrictLower

/-- Both endpoints have zero magnitude in one signed half. -/
def bothZeroBits (values : List Nat) : List Bool :=
  pairwise .conjunction
    (AlignedBooleanListClosure.negated
      (UnaryFieldPairPresence.fieldBits .first values))
    (AlignedBooleanListClosure.negated
      (UnaryFieldPairPresence.fieldBits .second values))

def nonnegativeCase (positive negative : List Nat) : List Bool :=
  pairwise .conjunction
    (UnaryFieldSuccessorRows.bits false positive)
    (bothZeroBits negative)

def negativeCase (positive negative : List Nat) : List Bool :=
  pairwise .conjunction
    (UnaryFieldSuccessorRows.bits true negative)
    (bothZeroBits positive)

/-- Mark ordered pairs whose represented second signed integer is the
successor of the first. -/
def bits (positive negative : List Nat) : List Bool :=
  pairwise .disjunction
    (nonnegativeCase positive negative)
    (negativeCase positive negative)

@[simp] theorem bothZeroBits_length (values : List Nat) :
    (bothZeroBits values).length = values.length ^ 2 := by
  simp [bothZeroBits]

@[simp] theorem nonnegativeCase_length
    {positive negative : List Nat}
    (lengthEq : positive.length = negative.length) :
    (nonnegativeCase positive negative).length = positive.length ^ 2 := by
  simp [nonnegativeCase, lengthEq]

@[simp] theorem negativeCase_length
    {positive negative : List Nat}
    (lengthEq : positive.length = negative.length) :
    (negativeCase positive negative).length = positive.length ^ 2 := by
  simp [negativeCase, lengthEq]

@[simp] theorem bits_length
    {positive negative : List Nat}
    (lengthEq : positive.length = negative.length) :
    (bits positive negative).length = positive.length ^ 2 := by
  simp [bits, lengthEq]

end SignedUnarySuccessor
end LeanTrominoes
