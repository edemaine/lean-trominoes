import LeanTrominoes.PartrecPair
import LeanTrominoes.PartrecAddSpace
import LeanTrominoes.PartrecMultiplySpace
import LeanTrominoes.PartrecNatCompareSpace

/-!
# Evaluator-space composition for forward pairing

This file fits the explicit squares, sums, and strict-comparison branch used
by `natPairCode`.  The certificate is continuation-independent and exposes
the exact cost of the branch selected by the defining equation of `Nat.pair`.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def natPairLeftSquareArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [left] [left]
    (getCost 0 [left, right]) (getCost 0 [left, right])

theorem natPairLeftSquareArguments (left right : Nat) :
    EvaluatorCodeFits Code.natPairLeftSquareArgumentsCode
      [left, right] [left, left]
      (natPairLeftSquareArgumentsCost left right) := by
  simpa [Code.natPairLeftSquareArgumentsCode,
    natPairLeftSquareArgumentsCost, prependCost] using
    prepend (get 0 [left, right]) (get 0 [left, right])

def natPairRightSquareArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [right] [right]
    (getCost 1 [left, right]) (getCost 1 [left, right])

theorem natPairRightSquareArguments (left right : Nat) :
    EvaluatorCodeFits Code.natPairRightSquareArgumentsCode
      [left, right] [right, right]
      (natPairRightSquareArgumentsCost left right) := by
  simpa [Code.natPairRightSquareArgumentsCode,
    natPairRightSquareArgumentsCost, prependCost] using
    prepend (get 1 [left, right]) (get 1 [left, right])

def natPairLeftSquareCost (left right : Nat) : Nat :=
  natMultiplyCost left left +
    natPairLeftSquareArgumentsCost left right

theorem natPairLeftSquare (left right : Nat) :
    EvaluatorCodeFits Code.natPairLeftSquareCode
      [left, right] [left * left]
      (natPairLeftSquareCost left right) := by
  simpa [Code.natPairLeftSquareCode,
    natPairLeftSquareCost] using
    comp (natMultiply left left)
      (natPairLeftSquareArguments left right)

def natPairRightSquareCost (left right : Nat) : Nat :=
  natMultiplyCost right right +
    natPairRightSquareArgumentsCost left right

theorem natPairRightSquare (left right : Nat) :
    EvaluatorCodeFits Code.natPairRightSquareCode
      [left, right] [right * right]
      (natPairRightSquareCost left right) := by
  simpa [Code.natPairRightSquareCode,
    natPairRightSquareCost] using
    comp (natMultiply right right)
      (natPairRightSquareArguments left right)

def natPairLowerArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [right * right] [left]
    (natPairRightSquareCost left right)
    (getCost 0 [left, right])

theorem natPairLowerArguments (left right : Nat) :
    EvaluatorCodeFits Code.natPairLowerArgumentsCode
      [left, right] [right * right, left]
      (natPairLowerArgumentsCost left right) := by
  simpa [Code.natPairLowerArgumentsCode,
    natPairLowerArgumentsCost, prependCost] using
    prepend (natPairRightSquare left right)
      (get 0 [left, right])

def natPairLowerCost (left right : Nat) : Nat :=
  natAddCost (right * right) left +
    natPairLowerArgumentsCost left right

theorem natPairLower (left right : Nat) :
    EvaluatorCodeFits Code.natPairLowerCode
      [left, right] [right * right + left]
      (natPairLowerCost left right) := by
  simpa [Code.natPairLowerCode, natPairLowerCost] using
    comp (natAdd (right * right) left)
      (natPairLowerArguments left right)

def natPairUpperFirstArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [left * left] [left]
    (natPairLeftSquareCost left right)
    (getCost 0 [left, right])

theorem natPairUpperFirstArguments (left right : Nat) :
    EvaluatorCodeFits Code.natPairUpperFirstArgumentsCode
      [left, right] [left * left, left]
      (natPairUpperFirstArgumentsCost left right) := by
  simpa [Code.natPairUpperFirstArgumentsCode,
    natPairUpperFirstArgumentsCost, prependCost] using
    prepend (natPairLeftSquare left right)
      (get 0 [left, right])

def natPairUpperFirstCost (left right : Nat) : Nat :=
  natAddCost (left * left) left +
    natPairUpperFirstArgumentsCost left right

theorem natPairUpperFirst (left right : Nat) :
    EvaluatorCodeFits Code.natPairUpperFirstCode
      [left, right] [left * left + left]
      (natPairUpperFirstCost left right) := by
  simpa [Code.natPairUpperFirstCode,
    natPairUpperFirstCost] using
    comp (natAdd (left * left) left)
      (natPairUpperFirstArguments left right)

def natPairUpperArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [left * left + left] [right]
    (natPairUpperFirstCost left right)
    (getCost 1 [left, right])

theorem natPairUpperArguments (left right : Nat) :
    EvaluatorCodeFits Code.natPairUpperArgumentsCode
      [left, right] [left * left + left, right]
      (natPairUpperArgumentsCost left right) := by
  simpa [Code.natPairUpperArgumentsCode,
    natPairUpperArgumentsCost, prependCost] using
    prepend (natPairUpperFirst left right)
      (get 1 [left, right])

def natPairUpperCost (left right : Nat) : Nat :=
  natAddCost (left * left + left) right +
    natPairUpperArgumentsCost left right

theorem natPairUpper (left right : Nat) :
    EvaluatorCodeFits Code.natPairUpperCode
      [left, right] [left * left + left + right]
      (natPairUpperCost left right) := by
  simpa [Code.natPairUpperCode, natPairUpperCost] using
    comp (natAdd (left * left + left) right)
      (natPairUpperArguments left right)

def natPairCost (left right : Nat) : Nat :=
  if left < right then
    branchZeroSuccCost [left, right] [Nat.pair left right]
      1 (natLtCost left right) (natPairLowerCost left right)
  else
    branchZeroZeroCost [left, right] [Nat.pair left right]
      0 (natLtCost left right) (natPairUpperCost left right)

/-- Exact fitted certificate for the standard forward pairing program. -/
theorem natPair (left right : Nat) :
    EvaluatorCodeFits Code.natPairCode
      [left, right] [Nat.pair left right]
      (natPairCost left right) := by
  by_cases less : left < right
  · have testFit :
        EvaluatorCodeFits Code.natLtCode [left, right] [1]
          (natLtCost left right) := by
        simpa [less] using natLt left right
    have branch := branchZero_succ
      (whenZero := Code.natPairUpperCode)
      (show 0 < 1 by omega)
      testFit (natPairLower left right)
    simpa [Code.natPairCode, natPairCost,
      Nat.pair, less] using branch
  · have testFit :
        EvaluatorCodeFits Code.natLtCode [left, right] [0]
          (natLtCost left right) := by
        simpa [less] using natLt left right
    have branch := branchZero_zero
      (whenSucc := Code.natPairLowerCode) rfl
      testFit (natPairUpper left right)
    simpa [Code.natPairCode, natPairCost,
      Nat.pair, less] using branch

/-- One arithmetic envelope containing both inputs, both possible squares,
and the final paired value. -/
def natPairLimit (left right : Nat) : Nat :=
  64 * (left + right + left * left + right * right +
    Nat.pair left right + 100) + 1000

/-- Uniform workspace unit for forward pairing. -/
def natPairUnit (left right : Nat) : Nat :=
  encodedListSpace [natPairLimit left right] + 1

private theorem natPairValueBits_le_unit
    (left right value : Nat)
    (bound : value ≤ natPairLimit left right) :
    (Computability.encodeNat value).length ≤
      natPairUnit left right := by
  have bits := encodeNat_length_mono bound
  simp [natPairUnit, encodedListSpace_cons,
    encodedListSpace_nil]
  omega

private theorem natPairArgumentsCost_le_unit
    (left right : Nat) :
    natPairLeftSquareArgumentsCost left right ≤
        1000000 * natPairUnit left right ∧
      natPairRightSquareArgumentsCost left right ≤
        1000000 * natPairUnit left right := by
  have leftBound : left ≤ natPairLimit left right := by
    simp only [natPairLimit]
    omega
  have rightBound : right ≤ natPairLimit left right := by
    simp only [natPairLimit]
    omega
  have leftBits := natPairValueBits_le_unit
    left right left leftBound
  have rightBits := natPairValueBits_le_unit
    left right right rightBound
  have leftSuccBits := natPairValueBits_le_unit left right (left + 1)
    (by simp only [natPairLimit]; omega)
  have rightSuccBits := natPairValueBits_le_unit left right (right + 1)
    (by simp only [natPairLimit]; omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have unitPositive : 1 ≤ natPairUnit left right := by
    simp [natPairUnit]
  constructor <;>
    simp [natPairLeftSquareArgumentsCost,
      natPairRightSquareArgumentsCost,
      prependCost, getCost, dropCost, idCost,
      headCost, nilCost, tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits] at * <;>
    omega

private theorem natPairLeftSquareCost_le_unit
    (left right : Nat) :
    natPairLeftSquareCost left right ≤
      2000000000000000000000000000000000000 *
        natPairUnit left right := by
  have multiplyLocal := natMultiplyCost_le_linear left left
  let small := 16 * (left + left + left * left + 10) + 100
  have smallBound : small ≤ natPairLimit left right := by
    simp only [small, natPairLimit]
    omega
  have bits := encodeNat_length_mono smallBound
  have unitBound :
      encodedListSpace [small] + 1 ≤ natPairUnit left right := by
    simpa [small, natPairUnit,
      encodedListSpace_cons, encodedListSpace_nil] using bits
  have multiplyGlobal :
      natMultiplyCost left left ≤
        1000000000000000000000000000000000000 *
          natPairUnit left right := by
    exact multiplyLocal.trans
      (Nat.mul_le_mul_left _ unitBound)
  have arguments := (natPairArgumentsCost_le_unit left right).1
  simp only [natPairLeftSquareCost]
  omega

private theorem natPairRightSquareCost_le_unit
    (left right : Nat) :
    natPairRightSquareCost left right ≤
      2000000000000000000000000000000000000 *
        natPairUnit left right := by
  have multiplyLocal := natMultiplyCost_le_linear right right
  let small := 16 * (right + right + right * right + 10) + 100
  have smallBound : small ≤ natPairLimit left right := by
    simp only [small, natPairLimit]
    omega
  have bits := encodeNat_length_mono smallBound
  have unitBound :
      encodedListSpace [small] + 1 ≤ natPairUnit left right := by
    simpa [small, natPairUnit,
      encodedListSpace_cons, encodedListSpace_nil] using bits
  have multiplyGlobal :
      natMultiplyCost right right ≤
        1000000000000000000000000000000000000 *
          natPairUnit left right := by
    exact multiplyLocal.trans
      (Nat.mul_le_mul_left _ unitBound)
  have arguments := (natPairArgumentsCost_le_unit left right).2
  simp only [natPairRightSquareCost]
  omega

private theorem natPairLowerCost_le_unit
    (left right : Nat) :
    natPairLowerCost left right ≤
      3000000000000000000000000000000000000 *
        natPairUnit left right := by
  have squareCost := natPairRightSquareCost_le_unit left right
  have addLocal := natAddCost_le_linear (right * right) left
  let small := 2 * (right * right + left) + 4
  have smallBound : small ≤ natPairLimit left right := by
    simp only [small, natPairLimit]
    omega
  have smallBits := encodeNat_length_mono smallBound
  have addUnit :
      encodedListSpace [small] + 1 ≤ natPairUnit left right := by
    simpa [small, natPairUnit,
      encodedListSpace_cons, encodedListSpace_nil] using smallBits
  have addGlobal :
      natAddCost (right * right) left ≤
        100000000 * natPairUnit left right :=
    addLocal.trans (Nat.mul_le_mul_left _ addUnit)
  have leftBits := natPairValueBits_le_unit left right left
    (by simp only [natPairLimit]; omega)
  have rightBits := natPairValueBits_le_unit left right right
    (by simp only [natPairLimit]; omega)
  have leftSuccBits := natPairValueBits_le_unit left right (left + 1)
    (by simp only [natPairLimit]; omega)
  have rightSquareBits := natPairValueBits_le_unit
    left right (right * right)
    (by simp only [natPairLimit]; omega)
  have rightSquareSuccBits := natPairValueBits_le_unit
    left right (right * right + 1)
    (by simp only [natPairLimit]; omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have unitPositive : 1 ≤ natPairUnit left right := by
    simp [natPairUnit]
  have argumentCost :
      natPairLowerArgumentsCost left right ≤
        2500000000000000000000000000000000000 *
          natPairUnit left right := by
    simp [natPairLowerArgumentsCost, prependCost,
      getCost, dropCost, idCost, headCost, nilCost,
      tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits] at *
    omega
  simp only [natPairLowerCost]
  omega

private theorem natPairUpperCost_le_unit
    (left right : Nat) :
    natPairUpperCost left right ≤
      5000000000000000000000000000000000000 *
        natPairUnit left right := by
  have squareCost := natPairLeftSquareCost_le_unit left right
  have firstAddLocal := natAddCost_le_linear (left * left) left
  have secondAddLocal :=
    natAddCost_le_linear (left * left + left) right
  let firstSmall := 2 * (left * left + left) + 4
  let secondSmall := 2 * (left * left + left + right) + 4
  have firstSmallBound : firstSmall ≤ natPairLimit left right := by
    simp only [firstSmall, natPairLimit]
    omega
  have secondSmallBound : secondSmall ≤ natPairLimit left right := by
    simp only [secondSmall, natPairLimit]
    omega
  have firstBits := encodeNat_length_mono firstSmallBound
  have secondBits := encodeNat_length_mono secondSmallBound
  have firstUnit :
      encodedListSpace [firstSmall] + 1 ≤ natPairUnit left right := by
    simpa [firstSmall, natPairUnit,
      encodedListSpace_cons, encodedListSpace_nil] using firstBits
  have secondUnit :
      encodedListSpace [secondSmall] + 1 ≤ natPairUnit left right := by
    simpa [secondSmall, natPairUnit,
      encodedListSpace_cons, encodedListSpace_nil] using secondBits
  have firstAdd :
      natAddCost (left * left) left ≤
        100000000 * natPairUnit left right :=
    firstAddLocal.trans (Nat.mul_le_mul_left _ firstUnit)
  have secondAdd :
      natAddCost (left * left + left) right ≤
        100000000 * natPairUnit left right :=
    secondAddLocal.trans (Nat.mul_le_mul_left _ secondUnit)
  have leftBits := natPairValueBits_le_unit left right left
    (by simp only [natPairLimit]; omega)
  have rightBits := natPairValueBits_le_unit left right right
    (by simp only [natPairLimit]; omega)
  have leftSuccBits := natPairValueBits_le_unit left right (left + 1)
    (by simp only [natPairLimit]; omega)
  have rightSuccBits := natPairValueBits_le_unit left right (right + 1)
    (by simp only [natPairLimit]; omega)
  have squareBits := natPairValueBits_le_unit
    left right (left * left)
    (by simp only [natPairLimit]; omega)
  have firstSumBits := natPairValueBits_le_unit
    left right (left * left + left)
    (by simp only [natPairLimit]; omega)
  have squareSuccBits := natPairValueBits_le_unit
    left right (left * left + 1)
    (by simp only [natPairLimit]; omega)
  have firstSumSuccBits := natPairValueBits_le_unit
    left right (left * left + left + 1)
    (by simp only [natPairLimit]; omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have unitPositive : 1 ≤ natPairUnit left right := by
    simp [natPairUnit]
  have firstArguments :
      natPairUpperFirstArgumentsCost left right ≤
        2500000000000000000000000000000000000 *
          natPairUnit left right := by
    simp [natPairUpperFirstArgumentsCost,
      prependCost, getCost, dropCost, idCost,
      headCost, nilCost, tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits] at *
    omega
  have firstCost :
      natPairUpperFirstCost left right ≤
        3000000000000000000000000000000000000 *
          natPairUnit left right := by
    simp only [natPairUpperFirstCost]
    omega
  have argumentsCost :
      natPairUpperArgumentsCost left right ≤
        4000000000000000000000000000000000000 *
          natPairUnit left right := by
    simp [natPairUpperArgumentsCost,
      prependCost, getCost, dropCost, idCost,
      headCost, nilCost, tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits] at *
    omega
  simp only [natPairUpperCost]
  omega

set_option maxHeartbeats 1500000 in
/-- Forward pairing has evaluator space linear in one encoded arithmetic
envelope containing its inputs and output. -/
theorem natPairCost_le_linear (left right : Nat) :
    natPairCost left right ≤
      10000000000000000000000000000000000000000 *
        natPairUnit left right := by
  have testLocal := natLtCost_le_linear left right
  let testLimit := 2 * (left + right) + 4
  have testLimitBound : testLimit ≤ natPairLimit left right := by
    simp only [testLimit, natPairLimit]
    omega
  have testBits := encodeNat_length_mono testLimitBound
  have testUnit :
      encodedListSpace [testLimit] + 1 ≤ natPairUnit left right := by
    simpa [testLimit, natPairUnit,
      encodedListSpace_cons, encodedListSpace_nil] using testBits
  have testCost :
      natLtCost left right ≤
        1000000000 * natPairUnit left right :=
    testLocal.trans (Nat.mul_le_mul_left _ testUnit)
  have lowerCost := natPairLowerCost_le_unit left right
  have upperCost := natPairUpperCost_le_unit left right
  have leftBits := natPairValueBits_le_unit left right left
    (by simp only [natPairLimit]; omega)
  have rightBits := natPairValueBits_le_unit left right right
    (by simp only [natPairLimit]; omega)
  have pairBits := natPairValueBits_le_unit
    left right (Nat.pair left right)
    (by simp only [natPairLimit]; omega)
  have leftSuccBits := natPairValueBits_le_unit left right (left + 1)
    (by simp only [natPairLimit]; omega)
  have rightSuccBits := natPairValueBits_le_unit left right (right + 1)
    (by simp only [natPairLimit]; omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have unitPositive : 1 ≤ natPairUnit left right := by
    simp [natPairUnit]
  by_cases less : left < right <;>
    simp [natPairCost, less, branchZeroZeroCost,
      branchZeroSuccCost, branchZeroTestCost,
      prependCost, idCost, zeroPrimeCost, tailCost,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits, oneBits] at * <;>
    omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
