/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecDynamicDropSpace
import LeanTrominoes.PartrecMultiplySpace
import LeanTrominoes.PartrecFlatSavitchContext

/-!
# Evaluator-space certificate for flat Savitch context recovery

The suffix-preserving Savitch state has seven fixed fields and six fields per
continuation frame.  This module fits the runtime offset calculation and the
dynamic suffix drop, then bounds the complete recovery program in the encoded
footprint of its native list input.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.FiniteState

namespace EvaluatorCodeFits

def flatContextFrameProductArgumentsCost
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) : Nat :=
  let values := divideEvalProgramList context stateCount state ++ suffix
  prependCost values [6] [state.stack.length]
    (numeralCost 6 values) (getCost 2 values)

theorem flatContextFrameProductArguments
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    EvaluatorCodeFits
      DivideEvalPartrec.flatContextFrameProductArgumentsCode
      (divideEvalProgramList context stateCount state ++ suffix)
      [6, state.stack.length]
      (flatContextFrameProductArgumentsCost
        context stateCount state suffix) := by
  let values := divideEvalProgramList context stateCount state ++ suffix
  have result := prepend (numeral 6 values) (get 2 values)
  simpa [DivideEvalPartrec.flatContextFrameProductArgumentsCode,
    DivideEvalPartrec.field, flatContextFrameProductArgumentsCost,
    values, divideEvalProgramList, DivideEvalState.toNatList,
    prependCost] using result

def flatContextFrameProductCost
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) : Nat :=
  natMultiplyCost 6 state.stack.length +
    flatContextFrameProductArgumentsCost context stateCount state suffix

theorem flatContextFrameProduct
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    EvaluatorCodeFits DivideEvalPartrec.flatContextFrameProductCode
      (divideEvalProgramList context stateCount state ++ suffix)
      [6 * state.stack.length]
      (flatContextFrameProductCost context stateCount state suffix) := by
  have result := comp (natMultiply 6 state.stack.length)
    (flatContextFrameProductArguments context stateCount state suffix)
  simpa [DivideEvalPartrec.flatContextFrameProductCode,
    flatContextFrameProductCost] using result

def flatContextOffsetCost
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) : Nat :=
  addConstCost 7 [6 * state.stack.length] +
    flatContextFrameProductCost context stateCount state suffix

theorem flatContextOffset
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    EvaluatorCodeFits DivideEvalPartrec.flatContextOffsetCode
      (divideEvalProgramList context stateCount state ++ suffix)
      [7 + 6 * state.stack.length]
      (flatContextOffsetCost context stateCount state suffix) := by
  have result := comp (addConst 7 [6 * state.stack.length])
    (flatContextFrameProduct context stateCount state suffix)
  simpa [DivideEvalPartrec.flatContextOffsetCode,
    flatContextOffsetCost, Nat.add_comm] using result

def flatContextDropInputCost
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) : Nat :=
  let values := divideEvalProgramList context stateCount state ++ suffix
  prependCost values [7 + 6 * state.stack.length] values
    (flatContextOffsetCost context stateCount state suffix)
    (idCost values)

theorem flatContextDropInput
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    let values := divideEvalProgramList context stateCount state ++ suffix
    EvaluatorCodeFits DivideEvalPartrec.flatContextDropInputCode values
      ((7 + 6 * state.stack.length) :: values)
      (flatContextDropInputCost context stateCount state suffix) := by
  simp only
  let values := divideEvalProgramList context stateCount state ++ suffix
  have result := prepend
    (flatContextOffset context stateCount state suffix) (id values)
  simpa [DivideEvalPartrec.flatContextDropInputCode,
    flatContextDropInputCost, values, prependCost] using result

def flatContextCost
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) : Nat :=
  let values := divideEvalProgramList context stateCount state ++ suffix
  dynamicDropCost (7 + 6 * state.stack.length) values +
    flatContextDropInputCost context stateCount state suffix

/-- Exact fitted certificate for recovering the arbitrary native-list suffix
after a variable-depth Savitch stack. -/
theorem flatContext
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    EvaluatorCodeFits DivideEvalPartrec.flatContextCode
      (divideEvalProgramList context stateCount state ++ suffix)
      suffix (flatContextCost context stateCount state suffix) := by
  let values := divideEvalProgramList context stateCount state ++ suffix
  let offset := 7 + 6 * state.stack.length
  have dropped := comp (dynamicDrop offset values)
    (flatContextDropInput context stateCount state suffix)
  have prefixLength := divideEvalProgramList_length context stateCount state
  have output : values.drop offset = suffix := by
    simp [values, offset, prefixLength]
  rw [output] at dropped
  simpa [DivideEvalPartrec.flatContextCode, flatContextCost,
    values, offset] using dropped

/-! ## Native input-space bound -/

def flatContextSpaceUnit
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) : Nat :=
  encodedListSpace
    (divideEvalProgramList context stateCount state ++ suffix) + 10

private theorem flatContextSpaceUnit_large
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    10 ≤ flatContextSpaceUnit context stateCount state suffix := by
  simp [flatContextSpaceUnit]

private theorem flatContextInputSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    encodedListSpace
        (divideEvalProgramList context stateCount state ++ suffix) ≤
      flatContextSpaceUnit context stateCount state suffix := by
  simp [flatContextSpaceUnit]

private theorem flatContextStackLengthSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    encodedListSpace [state.stack.length] ≤
      flatContextSpaceUnit context stateCount state suffix := by
  rcases state with ⟨⟨depth, first, last⟩, stack, answer⟩
  simp [flatContextSpaceUnit, divideEvalProgramList,
    DivideEvalState.toNatList, encodedListSpace_cons,
    FiniteState.encodedListSpace_append]
  omega

private theorem flatContextIdCost_le_linear (values : List Nat) :
    idCost values ≤ 10 * (encodedListSpace values + 1) := by
  have tailSpace := listCodeEncodedListSpace_tail_le (0 :: values)
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  simp [idCost, tailCost, zeroPrimeCost,
    encodedListSpace_cons, zeroBits] at tailSpace ⊢
  omega

private theorem flatContextFrameProductArgumentsCost_le_linear
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    flatContextFrameProductArgumentsCost context stateCount state suffix ≤
      1000000000 * flatContextSpaceUnit context stateCount state suffix := by
  let values := divideEvalProgramList context stateCount state ++ suffix
  let unit := flatContextSpaceUnit context stateCount state suffix
  have inputSpace : encodedListSpace values ≤ unit := by
    simpa [values, unit] using
      flatContextInputSpace_le_unit context stateCount state suffix
  have stackSpace : encodedListSpace [state.stack.length] ≤ unit := by
    simpa [unit] using
      flatContextStackLengthSpace_le_unit context stateCount state suffix
  have unitLarge : 10 ≤ unit := by
    simpa [unit] using flatContextSpaceUnit_large context stateCount state suffix
  have numeralAdd : addConstCost 6 [0] ≤ 1000000 := by native_decide
  have zeroRaw := listCodeZeroCost_le_linear values
  have numeralBound : numeralCost 6 values ≤ 1000000 * unit := by
    simp only [numeralCost]
    omega
  have getRaw := listCodeGetCost_le_linear 2 values
  have getBound : getCost 2 values ≤ 100000 * unit := by
    exact getRaw.trans (by omega)
  have outputSpace : encodedListSpace [6, state.stack.length] ≤
      3 * unit := by
    have sixBits : (Computability.encodeNat 6).length = 3 := by native_decide
    simp only [encodedListSpace_cons, encodedListSpace_nil] at stackSpace ⊢
    omega
  have estimate := listCodePrependCost_le_of values [6]
    [state.stack.length] (numeralCost 6 values) (getCost 2 values)
    (3 * unit) (by omega) (by
      have sixBits : (Computability.encodeNat 6).length = 3 := by native_decide
      simp only [encodedListSpace_cons, encodedListSpace_nil]
      omega) (by simpa only [List.headI_cons] using outputSpace)
  change prependCost values [6] [state.stack.length]
      (numeralCost 6 values) (getCost 2 values) ≤ _
  omega

private theorem flatContextFrameProductCost_le_linear
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    flatContextFrameProductCost context stateCount state suffix ≤
      1000000000000000000000000000000000000000000000000000000000000 *
        flatContextSpaceUnit context stateCount state suffix := by
  let unit := flatContextSpaceUnit context stateCount state suffix
  let stackLength := state.stack.length
  have stackSpace := flatContextStackLengthSpace_le_unit
    context stateCount state suffix
  have stackBits : (Computability.encodeNat stackLength).length ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at stackSpace
    dsimp only [stackLength]
    omega
  have stackBits' :
      (Computability.encodeNat state.stack.length).length ≤ unit := by
    simpa [stackLength] using stackBits
  have sum1 := encodeNat_add_length_le_sum 6 stackLength
  have product := encodeNat_mul_length_le_sum 6 stackLength
  have sum2 := encodeNat_add_length_le_sum (6 + stackLength)
    (6 * stackLength)
  have sum3 := encodeNat_add_length_le_sum
    (6 + stackLength + 6 * stackLength) 10
  have scaled := encodeNat_mul_length_le_sum 16
    (6 + stackLength + 6 * stackLength + 10)
  have final := encodeNat_add_length_le_sum
    (16 * (6 + stackLength + 6 * stackLength + 10)) 100
  have sixBits : (Computability.encodeNat 6).length = 3 := by native_decide
  have tenBits : (Computability.encodeNat 10).length = 4 := by native_decide
  have sixteenBits : (Computability.encodeNat 16).length = 5 := by native_decide
  have hundredBits : (Computability.encodeNat 100).length = 7 := by native_decide
  have unitLarge : 10 ≤ unit := by
    simpa [unit] using flatContextSpaceUnit_large context stateCount state suffix
  have multiplyRaw := natMultiplyCost_le_linear 6 stackLength
  have multiplyBound : natMultiplyCost 6 stackLength ≤
      1000000000000000000000000000000000000000000 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at multiplyRaw
    omega
  have arguments := flatContextFrameProductArgumentsCost_le_linear
    context stateCount state suffix
  have arguments' :
      flatContextFrameProductArgumentsCost context stateCount state suffix ≤
        1000000000 * unit := by simpa [unit] using arguments
  have multiplyBound' : natMultiplyCost 6 state.stack.length ≤
      1000000000000000000000000000000000000000000 * unit := by
    simpa [stackLength] using multiplyBound
  simp only [flatContextFrameProductCost]
  omega

private theorem flatContextOffsetSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    encodedListSpace [7 + 6 * state.stack.length] ≤
      20 * flatContextSpaceUnit context stateCount state suffix := by
  let unit := flatContextSpaceUnit context stateCount state suffix
  let stackLength := state.stack.length
  have stackSpace := flatContextStackLengthSpace_le_unit
    context stateCount state suffix
  have stackBits : (Computability.encodeNat stackLength).length ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at stackSpace
    dsimp only [stackLength]
    omega
  have stackBits' :
      (Computability.encodeNat state.stack.length).length ≤ unit := by
    simpa [stackLength] using stackBits
  have product := encodeNat_mul_length_le_sum 6 stackLength
  have final := encodeNat_add_length_le_sum 7 (6 * stackLength)
  have sixBits : (Computability.encodeNat 6).length = 3 := by native_decide
  have sevenBits : (Computability.encodeNat 7).length = 3 := by native_decide
  have unitLarge : 10 ≤ unit := by
    simpa [unit] using flatContextSpaceUnit_large context stateCount state suffix
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  dsimp only [stackLength] at product final ⊢
  omega

private theorem flatContextOffsetCost_le_linear
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    flatContextOffsetCost context stateCount state suffix ≤
      10000000000000000000000000000000000000000000000000000000000000 *
        flatContextSpaceUnit context stateCount state suffix := by
  let unit := flatContextSpaceUnit context stateCount state suffix
  have product := flatContextFrameProductCost_le_linear
    context stateCount state suffix
  have stackSpace := flatContextStackLengthSpace_le_unit
    context stateCount state suffix
  have productBits := encodeNat_mul_length_le_sum 6 state.stack.length
  have sixBits : (Computability.encodeNat 6).length = 3 := by native_decide
  have addRaw := addConstCost_le 7 [6 * state.stack.length]
  have unitLarge : 10 ≤ unit := by
    simpa [unit] using flatContextSpaceUnit_large context stateCount state suffix
  simp only [encodedListSpace_cons, encodedListSpace_nil] at stackSpace addRaw
  have addBound : addConstCost 7 [6 * state.stack.length] ≤
      100000 * unit := by
    omega
  have product' : flatContextFrameProductCost context stateCount state suffix ≤
      1000000000000000000000000000000000000000000000000000000000000 *
        unit := by simpa [unit] using product
  simp only [flatContextOffsetCost]
  omega

private theorem flatContextDropInputCost_le_linear
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    flatContextDropInputCost context stateCount state suffix ≤
      100000000000000000000000000000000000000000000000000000000000000 *
        flatContextSpaceUnit context stateCount state suffix := by
  let values := divideEvalProgramList context stateCount state ++ suffix
  let unit := flatContextSpaceUnit context stateCount state suffix
  let offset := 7 + 6 * state.stack.length
  have inputSpace : encodedListSpace values ≤ unit := by
    simpa [values, unit] using
      flatContextInputSpace_le_unit context stateCount state suffix
  have unitLarge : 10 ≤ unit := by
    simpa [unit] using flatContextSpaceUnit_large context stateCount state suffix
  have offsetSpace : encodedListSpace [offset] ≤ 20 * unit := by
    simpa [offset, unit] using
      flatContextOffsetSpace_le_unit context stateCount state suffix
  have outputSpace : encodedListSpace (offset :: values) ≤ 22 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at offsetSpace ⊢
    omega
  have offsetCost := flatContextOffsetCost_le_linear
    context stateCount state suffix
  have offsetCost' : flatContextOffsetCost context stateCount state suffix ≤
      10000000000000000000000000000000000000000000000000000000000000 *
        unit := by simpa [unit] using offsetCost
  have identityRaw := flatContextIdCost_le_linear values
  have identity : idCost values ≤ 100 * unit := by omega
  have estimate := listCodePrependCost_le_of values [offset] values
    (flatContextOffsetCost context stateCount state suffix) (idCost values)
    (22 * unit) (by omega) (by omega) (by
      simpa only [List.headI_cons] using outputSpace)
  change prependCost values [offset] values
      (flatContextOffsetCost context stateCount state suffix)
      (idCost values) ≤ _
  omega

/-- Linear native-input workspace bound for recovering the flat suffix. -/
def flatContextSpaceBound
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) : Nat :=
  1000000000000000000000000000000000000000000000000000000000000000 *
    flatContextSpaceUnit context stateCount state suffix

theorem flatContextCost_le_bound
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    flatContextCost context stateCount state suffix ≤
      flatContextSpaceBound context stateCount state suffix := by
  let values := divideEvalProgramList context stateCount state ++ suffix
  let unit := flatContextSpaceUnit context stateCount state suffix
  let offset := 7 + 6 * state.stack.length
  have inputSpace : encodedListSpace values ≤ unit := by
    simpa [values, unit] using
      flatContextInputSpace_le_unit context stateCount state suffix
  have offsetSpace : encodedListSpace [offset] ≤ 20 * unit := by
    simpa [offset, unit] using
      flatContextOffsetSpace_le_unit context stateCount state suffix
  have dynamic : dynamicDropCost offset values ≤ 100000000 * unit := by
    simp only [dynamicDropCost]
    simp only [encodedListSpace_cons, encodedListSpace_nil] at offsetSpace ⊢
    omega
  have input := flatContextDropInputCost_le_linear
    context stateCount state suffix
  have input' : flatContextDropInputCost context stateCount state suffix ≤
      100000000000000000000000000000000000000000000000000000000000000 *
        unit := by simpa [unit] using input
  have dynamic' : dynamicDropCost
      (7 + 6 * state.stack.length)
      (divideEvalProgramList context stateCount state ++ suffix) ≤
        100000000 * unit := by
    simpa [offset, values] using dynamic
  simp only [flatContextCost, flatContextSpaceBound]
  omega

theorem flatContextBounded
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    EvaluatorCodeFits DivideEvalPartrec.flatContextCode
      (divideEvalProgramList context stateCount state ++ suffix)
      suffix (flatContextSpaceBound context stateCount state suffix) :=
  (flatContext context stateCount state suffix).mono
    (flatContextCost_le_bound context stateCount state suffix)

end EvaluatorCodeFits
end PartrecToTM2
end Turing
