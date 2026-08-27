/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairData

/-! # Signed order-coordinate spans of rank-ordered carrier pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields

def orderWordPairs (field : Field) (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordPairs.Input :=
  DelimitedBinaryWordPairProductMachine.pairs
    (UnaryFieldBinaryWords.words (field.rankOrderedValues descriptors))

/-- Row-major truncated differences of one rank-ordered unary field.  When
`keepFirst` is false this is `second - first`; when it is true the arguments
are reversed. -/
def orderExcesses (field : Field) (keepFirst : Bool)
    (descriptors : List RouteDescriptor) : List Nat :=
  DelimitedBinaryWordPairExcessMachine.excesses keepFirst
    (orderWordPairs field descriptors)

/-- Row-major nonnegative signed differences of globally rank-ordered carrier
coordinates.  Positive and negative magnitudes are oriented oppositely before
being added. -/
def orderSpans (descriptors : List RouteDescriptor) : List Nat :=
  AlignedUnaryListClosure.added
    (orderExcesses .orderPositive false descriptors)
    (orderExcesses .orderNegative true descriptors)

private theorem orderedProduct_length {Value : Type*}
    (values : List Value) :
    (values.flatMap fun first =>
      values.map fun second => (first, second)).length = values.length ^ 2 := by
  simp [pow_two]

@[simp] theorem orderExcesses_length (field : Field) (keepFirst : Bool)
    (descriptors : List RouteDescriptor) :
    (orderExcesses field keepFirst descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  unfold orderExcesses orderWordPairs
  rw [show
    (DelimitedBinaryWordPairExcessMachine.excesses keepFirst
      (DelimitedBinaryWordPairProductMachine.pairs
        (UnaryFieldBinaryWords.words
          (field.rankOrderedValues descriptors)))).length =
      (DelimitedBinaryWordPairProductMachine.pairs
        (UnaryFieldBinaryWords.words
          (field.rankOrderedValues descriptors))).pairs.length
    by simp [DelimitedBinaryWordPairExcessMachine.excesses]]
  unfold DelimitedBinaryWordPairProductMachine.pairs
  rw [orderedProduct_length]
  simp [UnaryFieldBinaryWords.words]

@[simp] theorem orderSpans_length (descriptors : List RouteDescriptor) :
    (orderSpans descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [orderSpans]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
