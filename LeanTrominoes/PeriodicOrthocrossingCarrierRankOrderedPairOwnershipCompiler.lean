/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairFieldBitCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairOwnershipData

/-! # Compiler for ownership bits of rank-ordered carrier pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing

/-- Pointwise selection of two aligned compiled Boolean streams is
polynomial-time computable. -/
noncomputable def muxBitsComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (selector whenTrue whenFalse : Input → List Bool)
    (trueLength : ∀ input,
      (selector input).length = (whenTrue input).length)
    (falseLength : ∀ input,
      (selector input).length = (whenFalse input).length)
    (selectorCompiler :
      @TM2ComputableInPolyTime
        Input (List Bool) InputSymbol Bool encodeInput id selector)
    (whenTrueCompiler :
      @TM2ComputableInPolyTime
        Input (List Bool) InputSymbol Bool encodeInput id whenTrue)
    (whenFalseCompiler :
      @TM2ComputableInPolyTime
        Input (List Bool) InputSymbol Bool encodeInput id whenFalse) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => muxBits
        (selector input) (whenTrue input) (whenFalse input)) := by
  let notSelectorCompiler :=
    AlignedBooleanListClosure.mapNegatedComputableInPolyTime
      encodeInput selector selectorCompiler
  let trueBranchCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      encodeInput .conjunction selector whenTrue trueLength
      selectorCompiler whenTrueCompiler
  let falseBranchCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      encodeInput .conjunction
      (fun input => AlignedBooleanListClosure.negated (selector input))
      whenFalse
      (fun input => by simpa using falseLength input)
      notSelectorCompiler whenFalseCompiler
  exact AlignedBooleanListClosure.combinedComputableInPolyTime
    encodeInput .disjunction
    (fun input => combined (selector input) (whenTrue input))
    (fun input => combined
      (AlignedBooleanListClosure.negated (selector input))
      (whenFalse input))
    (fun input => by
      calc
        (combined (selector input) (whenTrue input)).length =
            (selector input).length := by
          simp [combined, trueLength input]
        _ = (combined
              (AlignedBooleanListClosure.negated (selector input))
              (whenFalse input)).length := by
          simp [combined, falseLength input])
    trueBranchCompiler falseBranchCompiler

noncomputable def endpointOwnershipZeroBitsComputableInPolyTime
    (side : UnaryFieldPairPresence.Side) :
    TM2ComputableInPolyTime InputEncoding id
      (endpointOwnershipZeroBits side) := by
  let horizontalCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      InputEncoding .conjunction
      (fieldZeroBits side .ownershipHorizontalPositive)
      (fieldZeroBits side .ownershipHorizontalNegative)
      (fun descriptors => by simp)
      (fieldZeroBitsComputableInPolyTime side
        .ownershipHorizontalPositive)
      (fieldZeroBitsComputableInPolyTime side
        .ownershipHorizontalNegative)
  let verticalCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      InputEncoding .conjunction
      (fieldZeroBits side .ownershipVerticalPositive)
      (fieldZeroBits side .ownershipVerticalNegative)
      (fun descriptors => by simp)
      (fieldZeroBitsComputableInPolyTime side .ownershipVerticalPositive)
      (fieldZeroBitsComputableInPolyTime side .ownershipVerticalNegative)
  exact AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction
    (fun descriptors => combined
      (fieldZeroBits side .ownershipHorizontalPositive descriptors)
      (fieldZeroBits side .ownershipHorizontalNegative descriptors))
    (fun descriptors => combined
      (fieldZeroBits side .ownershipVerticalPositive descriptors)
      (fieldZeroBits side .ownershipVerticalNegative descriptors))
    (fun descriptors => by simp [combined])
    horizontalCompiler verticalCompiler

noncomputable def firstOwnershipZeroBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id firstOwnershipZeroBits :=
  endpointOwnershipZeroBitsComputableInPolyTime .first

noncomputable def secondOwnershipZeroBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id secondOwnershipZeroBits :=
  endpointOwnershipZeroBitsComputableInPolyTime .second

/-- The exact representative-owner predicate for every globally rank-ordered
carrier pair is polynomial-time computable. -/
noncomputable def representativeBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id representativeBits := by
  let fallbackCompiler := muxBitsComputableInPolyTime
    InputEncoding secondBoundaryBits secondOwnershipZeroBits
    firstOwnershipZeroBits
    (fun descriptors => by
      simp [secondBoundaryBits, secondOwnershipZeroBits])
    (fun descriptors => by
      simp [secondBoundaryBits, firstOwnershipZeroBits])
    secondBoundaryBitsComputableInPolyTime
    secondOwnershipZeroBitsComputableInPolyTime
    firstOwnershipZeroBitsComputableInPolyTime
  exact muxBitsComputableInPolyTime
    InputEncoding firstBoundaryBits firstOwnershipZeroBits
    (fun descriptors => muxBits
      (secondBoundaryBits descriptors)
      (secondOwnershipZeroBits descriptors)
      (firstOwnershipZeroBits descriptors))
    (fun descriptors => by
      simp [firstBoundaryBits, firstOwnershipZeroBits])
    (fun descriptors => by
      simp [firstBoundaryBits, secondBoundaryBits,
        firstOwnershipZeroBits, secondOwnershipZeroBits, muxBits,
        combined])
    firstBoundaryBitsComputableInPolyTime
    firstOwnershipZeroBitsComputableInPolyTime fallbackCompiler

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end
