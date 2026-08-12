import LeanTrominoes.PartrecAddSpace
import LeanTrominoes.PartrecIntOffsetSpace
import LeanTrominoes.PartrecPackedColumnPhaseSpace
import LeanTrominoes.PartrecPackedTargetCell
import LeanTrominoes.PartrecPairSpace

/-!
# Evaluator-space certificate for canonical packed target cells

This file fits the complete target constructor: fixed-field projection,
wrapped column arithmetic, nonnegative integer encoding, fixed vertical
offset, and forward pairing into a `Cell` code.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def packedTargetColumnArgumentsTailCost
    (period phase column rowCode : Nat) : Nat :=
  let values := [period, phase, column, rowCode]
  prependCost values [phase] [column]
    (getCost 1 values) (getCost 2 values)

def packedTargetColumnArgumentsCost
    (period phase column rowCode : Nat) : Nat :=
  let values := [period, phase, column, rowCode]
  prependCost values [period] [phase, column]
    (getCost 0 values)
    (packedTargetColumnArgumentsTailCost
      period phase column rowCode)

theorem packedTargetColumnArguments
    (period phase column rowCode : Nat) :
    EvaluatorCodeFits Code.packedTargetColumnArgumentsCode
      [period, phase, column, rowCode]
      [period, phase, column]
      (packedTargetColumnArgumentsCost
        period phase column rowCode) := by
  let values := [period, phase, column, rowCode]
  have tailFit :
      EvaluatorCodeFits (Code.prepend (Code.get 1) (Code.get 2))
        values [phase, column]
        (packedTargetColumnArgumentsTailCost
          period phase column rowCode) := by
    simpa [packedTargetColumnArgumentsTailCost, values,
      prependCost] using
      prepend (get 1 values) (get 2 values)
  simpa [Code.packedTargetColumnArgumentsCode,
    packedTargetColumnArgumentsCost, values,
    prependCost] using
    prepend (get 0 values) tailFit

def packedTargetColumnPhaseCost
    (period phase column rowCode : Nat) : Nat :=
  packedColumnPhaseCost period phase column +
    packedTargetColumnArgumentsCost period phase column rowCode

theorem packedTargetColumnPhase
    (period phase column rowCode : Nat) :
    EvaluatorCodeFits Code.packedTargetColumnPhaseCode
      [period, phase, column, rowCode]
      [Code.packedColumnPhaseNumerator period phase column % period]
      (packedTargetColumnPhaseCost
        period phase column rowCode) := by
  simpa [Code.packedTargetColumnPhaseCode,
    packedTargetColumnPhaseCost] using
    comp (packedColumnPhase period phase column)
      (packedTargetColumnArguments period phase column rowCode)

def packedTargetXArgumentsCost
    (period phase column rowCode : Nat) : Nat :=
  let values := [period, phase, column, rowCode]
  let x := Code.packedColumnPhaseNumerator period phase column % period
  prependCost values [x] [x]
    (packedTargetColumnPhaseCost period phase column rowCode)
    (packedTargetColumnPhaseCost period phase column rowCode)

theorem packedTargetXArguments
    (period phase column rowCode : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column % period
    EvaluatorCodeFits Code.packedTargetXArgumentsCode
      [period, phase, column, rowCode] [x, x]
      (packedTargetXArgumentsCost
        period phase column rowCode) := by
  simp only
  simpa [Code.packedTargetXArgumentsCode,
    packedTargetXArgumentsCost, prependCost] using
    prepend
      (packedTargetColumnPhase period phase column rowCode)
      (packedTargetColumnPhase period phase column rowCode)

def packedTargetXCost
    (period phase column rowCode : Nat) : Nat :=
  let x := Code.packedColumnPhaseNumerator period phase column % period
  natAddCost x x +
    packedTargetXArgumentsCost period phase column rowCode

theorem packedTargetX
    (period phase column rowCode : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column % period
    EvaluatorCodeFits Code.packedTargetXCode
      [period, phase, column, rowCode] [2 * x]
      (packedTargetXCost period phase column rowCode) := by
  simp only
  simpa [Code.packedTargetXCode, packedTargetXCost,
    Nat.two_mul] using
    comp
      (natAdd
        (Code.packedColumnPhaseNumerator period phase column % period)
        (Code.packedColumnPhaseNumerator period phase column % period))
      (packedTargetXArguments period phase column rowCode)

def packedTargetYCost
    (verticalOffset : Int)
    (period phase column rowCode : Nat) : Nat :=
  intOffsetCost verticalOffset rowCode +
    getCost 3 [period, phase, column, rowCode]

theorem packedTargetY
    (verticalOffset : Int)
    (period phase column rowCode : Nat) :
    EvaluatorCodeFits (Code.packedTargetYCode verticalOffset)
      [period, phase, column, rowCode]
      [intOffsetResultCode verticalOffset rowCode]
      (packedTargetYCost verticalOffset
        period phase column rowCode) := by
  simpa [Code.packedTargetYCode,
    packedTargetYCost] using
    comp (intOffset verticalOffset rowCode)
      (get 3 [period, phase, column, rowCode])

def packedTargetCellArgumentsCost
    (verticalOffset : Int)
    (period phase column rowCode : Nat) : Nat :=
  let values := [period, phase, column, rowCode]
  let x := Code.packedColumnPhaseNumerator period phase column % period
  let yCode := intOffsetResultCode verticalOffset rowCode
  prependCost values [2 * x] [yCode]
    (packedTargetXCost period phase column rowCode)
    (packedTargetYCost verticalOffset period phase column rowCode)

theorem packedTargetCellArguments
    (verticalOffset : Int)
    (period phase column rowCode : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column % period
    let yCode := intOffsetResultCode verticalOffset rowCode
    EvaluatorCodeFits
      (Code.packedTargetCellArgumentsCode verticalOffset)
      [period, phase, column, rowCode]
      [2 * x, yCode]
      (packedTargetCellArgumentsCost verticalOffset
        period phase column rowCode) := by
  simp only
  simpa [Code.packedTargetCellArgumentsCode,
    packedTargetCellArgumentsCost, prependCost] using
    prepend (packedTargetX period phase column rowCode)
      (packedTargetY verticalOffset period phase column rowCode)

def packedTargetCellCost
    (verticalOffset : Int)
    (period phase column rowCode : Nat) : Nat :=
  let x := Code.packedColumnPhaseNumerator period phase column % period
  let yCode := intOffsetResultCode verticalOffset rowCode
  natPairCost (2 * x) yCode +
    packedTargetCellArgumentsCost verticalOffset
      period phase column rowCode

theorem packedTargetCell
    (verticalOffset : Int)
    (period phase column rowCode : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column % period
    let yCode := intOffsetResultCode verticalOffset rowCode
    EvaluatorCodeFits (Code.packedTargetCellCode verticalOffset)
      [period, phase, column, rowCode]
      [Nat.pair (2 * x) yCode]
      (packedTargetCellCost verticalOffset
        period phase column rowCode) := by
  simp only
  simpa [Code.packedTargetCellCode,
    packedTargetCellCost] using
    comp
      (natPair
        (2 * (Code.packedColumnPhaseNumerator
          period phase column % period))
        (intOffsetResultCode verticalOffset rowCode))
      (packedTargetCellArguments verticalOffset
        period phase column rowCode)

theorem packedTargetCell_encode
    (verticalOffset : Int)
    (period phase column : Nat) (row : Int) :
    let x := Code.packedColumnPhaseNumerator period phase column % period
    EvaluatorCodeFits (Code.packedTargetCellCode verticalOffset)
      [period, phase, column, Encodable.encode row]
      [Encodable.encode
        ((Int.ofNat x, row + verticalOffset) : Cell)]
      (packedTargetCellCost verticalOffset
        period phase column (Encodable.encode row)) := by
  simp only
  have fitted := packedTargetCell verticalOffset
    period phase column (Encodable.encode row)
  simpa only [intOffsetResultCode_encode,
    Encodable.encode_prod_val,
    IntEncoding.encode_ofNat] using fitted

def packedTargetAuxLimit
    (verticalOffset : Int)
    (period phase column rowCode : Nat) : Nat :=
  256 * (period + phase + column + rowCode +
    2 * intOffsetAmount verticalOffset + 64) + 1000

def packedTargetAuxUnit
    (verticalOffset : Int)
    (period phase column rowCode : Nat) : Nat :=
  encodedListSpace
    [packedTargetAuxLimit verticalOffset
      period phase column rowCode] + 1

def packedTargetCellUnit
    (verticalOffset : Int)
    (period phase column rowCode : Nat) : Nat :=
  let x := Code.packedColumnPhaseNumerator period phase column % period
  let yCode := intOffsetResultCode verticalOffset rowCode
  packedTargetAuxUnit verticalOffset period phase column rowCode +
    natPairUnit (2 * x) yCode

set_option maxHeartbeats 800000 in
/-- The target-cell construction unit is linear in the bit lengths of its
five native arithmetic inputs. -/
theorem packedTargetCellUnit_le_linear
    (verticalOffset : Int)
    (period phase column rowCode : Nat) :
    packedTargetCellUnit verticalOffset period phase column rowCode ≤
      100000 * ((Computability.encodeNat period).length +
        (Computability.encodeNat phase).length +
        (Computability.encodeNat column).length +
        (Computability.encodeNat rowCode).length +
        (Computability.encodeNat
          (intOffsetAmount verticalOffset)).length + 1) := by
  let amount := intOffsetAmount verticalOffset
  let numerator := Code.packedColumnPhaseNumerator period phase column
  let x := numerator % period
  let yCode := intOffsetResultCode verticalOffset rowCode
  let rawSum := period + phase + column + rowCode + 2 * amount + 64
  have twoAmount := encodeNat_mul_length_le_sum 2 amount
  have sum1 := encodeNat_add_length_le_sum period phase
  have sum2 := encodeNat_add_length_le_sum (period + phase) column
  have sum3 := encodeNat_add_length_le_sum
    (period + phase + column) rowCode
  have sum4 := encodeNat_add_length_le_sum
    (period + phase + column + rowCode) (2 * amount)
  have sum5 := encodeNat_add_length_le_sum
    (period + phase + column + rowCode + 2 * amount) 64
  have scaled := encodeNat_mul_length_le_sum 256 rawSum
  have auxLimitBits := encodeNat_add_length_le_sum
    (256 * rawSum) 1000
  have numeratorBound :
      numerator ≤ phase + column + (period + period) := by
    simp only [numerator, Code.packedColumnPhaseNumerator,
      Code.packedColumnPhaseSum]
    omega
  have xBound : x ≤ phase + column + (period + period) :=
    (Nat.mod_le numerator period).trans numeratorBound
  have periodDouble := encodeNat_add_length_le_sum period period
  have phaseColumn := encodeNat_add_length_le_sum phase column
  have xLimit := encodeNat_add_length_le_sum
    (phase + column) (period + period)
  have xBits := (encodeNat_length_mono xBound).trans xLimit
  have doubleX := encodeNat_mul_length_le_sum 2 x
  have yBits := intOffsetResultCode_length_le verticalOffset rowCode
  have pairUnit := natPairUnit_le_linear (2 * x) yCode
  have twoAmountRaw :
      (Computability.encodeNat
        (2 * intOffsetAmount verticalOffset)).length ≤
        (Computability.encodeNat 2).length +
          (Computability.encodeNat
            (intOffsetAmount verticalOffset)).length := by
    simpa [amount] using twoAmount
  have sum4Raw :
      (Computability.encodeNat
        (period + phase + column + rowCode +
          2 * intOffsetAmount verticalOffset)).length ≤
        (Computability.encodeNat
          (period + phase + column + rowCode)).length +
          (Computability.encodeNat
            (2 * intOffsetAmount verticalOffset)).length + 1 := by
    simpa [amount] using sum4
  have rawSumBitsRaw :
      (Computability.encodeNat
        (period + phase + column + rowCode +
          2 * intOffsetAmount verticalOffset + 64)).length ≤
        (Computability.encodeNat
          (period + phase + column + rowCode +
            2 * intOffsetAmount verticalOffset)).length +
          (Computability.encodeNat 64).length + 1 := by
    simpa [amount] using sum5
  have scaledBitsRaw :
      (Computability.encodeNat
        (256 * (period + phase + column + rowCode +
          2 * intOffsetAmount verticalOffset + 64))).length ≤
        (Computability.encodeNat 256).length +
          (Computability.encodeNat
            (period + phase + column + rowCode +
              2 * intOffsetAmount verticalOffset + 64)).length := by
    simpa [rawSum, amount] using scaled
  have auxLimitBitsRaw :
      (Computability.encodeNat
        (256 * (period + phase + column + rowCode +
          2 * intOffsetAmount verticalOffset + 64) + 1000)).length ≤
        (Computability.encodeNat 256).length +
          (Computability.encodeNat
            (period + phase + column + rowCode +
              2 * intOffsetAmount verticalOffset + 64)).length + 1 +
          (Computability.encodeNat 1000).length + 1 := by
    have raw :
        (Computability.encodeNat
          (256 * (period + phase + column + rowCode +
            2 * intOffsetAmount verticalOffset + 64) + 1000)).length ≤
          (Computability.encodeNat
            (256 * (period + phase + column + rowCode +
              2 * intOffsetAmount verticalOffset + 64))).length +
            (Computability.encodeNat 1000).length + 1 := by
      simpa [rawSum, amount] using auxLimitBits
    omega
  have xBitsRaw :
      (Computability.encodeNat
        (Code.packedColumnPhaseNumerator period phase column % period)).length ≤
        (Computability.encodeNat (phase + column)).length +
          (Computability.encodeNat (period + period)).length + 1 := by
    simpa [x, numerator] using xBits
  have doubleXRaw :
      (Computability.encodeNat
        (2 * (Code.packedColumnPhaseNumerator
          period phase column % period))).length ≤
        (Computability.encodeNat 2).length +
          (Computability.encodeNat
            (Code.packedColumnPhaseNumerator
              period phase column % period)).length := by
    simpa [x] using doubleX
  have yBitsRaw :
      (Computability.encodeNat
        (intOffsetResultCode verticalOffset rowCode)).length ≤
        10 * ((Computability.encodeNat rowCode).length +
          (Computability.encodeNat
            (intOffsetAmount verticalOffset)).length + 1) := by
    simpa using yBits
  have pairUnitRaw :
      natPairUnit
          (2 * (Code.packedColumnPhaseNumerator
            period phase column % period))
          (intOffsetResultCode verticalOffset rowCode) ≤
        100 * ((Computability.encodeNat
            (2 * (Code.packedColumnPhaseNumerator
              period phase column % period))).length +
          (Computability.encodeNat
            (intOffsetResultCode verticalOffset rowCode)).length + 1) := by
    simpa [x, yCode] using pairUnit
  have twoBits :
      (Computability.encodeNat 2).length = 2 := by native_decide
  have sixtyFourBits :
      (Computability.encodeNat 64).length = 7 := by native_decide
  have twoFiftySixBits :
      (Computability.encodeNat 256).length = 9 := by native_decide
  have thousandBits :
      (Computability.encodeNat 1000).length = 10 := by native_decide
  simp only [packedTargetCellUnit, packedTargetAuxUnit,
    packedTargetAuxLimit, encodedListSpace_cons,
    encodedListSpace_nil]
  change
    (Computability.encodeNat (256 * rawSum + 1000)).length + 2 +
        natPairUnit (2 * x) yCode ≤ _
  simp only [rawSum, amount, x, numerator, yCode]
  clear * - sum1 sum2 sum3 twoAmountRaw sum4Raw
    rawSumBitsRaw scaledBitsRaw auxLimitBitsRaw
    periodDouble phaseColumn xLimit xBitsRaw
    doubleXRaw yBitsRaw pairUnitRaw
    twoBits sixtyFourBits twoFiftySixBits thousandBits
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
/-- The complete canonical-cell constructor is linear in the sum of one
affine arithmetic envelope and the established forward-pairing envelope. -/
theorem packedTargetCellCost_le_linear
    (verticalOffset : Int)
    (period phase column rowCode : Nat) :
    packedTargetCellCost verticalOffset
        period phase column rowCode ≤
      1000000000000000000000000000000000000000000000 *
        (intOffsetAmount verticalOffset + 1) *
        packedTargetCellUnit verticalOffset
          period phase column rowCode := by
  let amount := intOffsetAmount verticalOffset
  let numerator :=
    Code.packedColumnPhaseNumerator period phase column
  let x := numerator % period
  let yCode := intOffsetResultCode verticalOffset rowCode
  let auxLimit := packedTargetAuxLimit verticalOffset
    period phase column rowCode
  let auxUnit := packedTargetAuxUnit verticalOffset
    period phase column rowCode
  let pairUnit := natPairUnit (2 * x) yCode
  let unit := packedTargetCellUnit verticalOffset
    period phase column rowCode
  let scaledUnit := (amount + 1) * unit
  change
    packedTargetCellCost verticalOffset
        period phase column rowCode ≤
      1000000000000000000000000000000000000000000000 *
        (amount + 1) * unit
  rw [Nat.mul_assoc]
  change
    packedTargetCellCost verticalOffset
        period phase column rowCode ≤
      1000000000000000000000000000000000000000000000 *
        scaledUnit

  have numeratorBound :
      numerator ≤ phase + column + (period + period) := by
    simp only [numerator, Code.packedColumnPhaseNumerator,
      Code.packedColumnPhaseSum]
    omega
  have xBound :
      x ≤ phase + column + (period + period) :=
    (Nat.mod_le numerator period).trans numeratorBound
  have yBound : yCode ≤ rowCode + 2 * amount := by
    simpa [yCode, amount] using
      intOffsetResultCode_le verticalOffset rowCode

  have periodBound : period ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have phaseBound : phase ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have columnBound : column ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have rowBound : rowCode ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have xAuxBound : x ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have doubleXBound : 2 * x ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have yAuxBound : yCode ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have periodSuccBound : period + 1 ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have phaseSuccBound : phase + 1 ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have columnSuccBound : column + 1 ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have rowSuccBound : rowCode + 1 ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have xSuccBound : x + 1 ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have doubleXSuccBound : 2 * x + 1 ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have ySuccBound : yCode + 1 ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega

  have phaseLimitBound :
      128 * (period + phase + column + 32) + 200 ≤
        auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have offsetLimitBound :
      2 * (rowCode + 2 * amount) + 8 ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega
  have addLimitBound :
      2 * (x + x) + 4 ≤ auxLimit := by
    simp only [auxLimit, packedTargetAuxLimit]
    omega

  have phaseLimitBits := encodeNat_length_mono phaseLimitBound
  have offsetLimitBits := encodeNat_length_mono offsetLimitBound
  have addLimitBits := encodeNat_length_mono addLimitBound
  have periodBits := encodeNat_length_mono periodBound
  have phaseBits := encodeNat_length_mono phaseBound
  have columnBits := encodeNat_length_mono columnBound
  have rowBits := encodeNat_length_mono rowBound
  have xBits := encodeNat_length_mono xAuxBound
  have doubleXBits := encodeNat_length_mono doubleXBound
  have yBits := encodeNat_length_mono yAuxBound
  have periodSuccBits := encodeNat_length_mono periodSuccBound
  have phaseSuccBits := encodeNat_length_mono phaseSuccBound
  have columnSuccBits := encodeNat_length_mono columnSuccBound
  have rowSuccBits := encodeNat_length_mono rowSuccBound
  have xSuccBits := encodeNat_length_mono xSuccBound
  have doubleXSuccBits := encodeNat_length_mono doubleXSuccBound
  have ySuccBits := encodeNat_length_mono ySuccBound

  have auxUnitEq :
      auxUnit = encodedListSpace [auxLimit] + 1 := by
    rfl
  have pairUnitEq : pairUnit = natPairUnit (2 * x) yCode := by
    rfl
  have unitEq : unit = auxUnit + pairUnit := by
    simp [unit, packedTargetCellUnit, auxUnit, pairUnit,
      x, yCode, numerator]
  have auxLeUnit : auxUnit ≤ unit := by
    rw [unitEq]
    omega
  have pairLeUnit : pairUnit ≤ unit := by
    rw [unitEq]
    omega
  have unitLeScaled : unit ≤ scaledUnit := by
    rw [show unit = 1 * unit by simp]
    exact Nat.mul_le_mul_right unit (by omega : 1 ≤ amount + 1)
  have auxLeScaled : auxUnit ≤ scaledUnit :=
    auxLeUnit.trans unitLeScaled
  have pairLeScaled : pairUnit ≤ scaledUnit :=
    pairLeUnit.trans unitLeScaled

  have phaseUnitLeAux :
      encodedListSpace
          [128 * (period + phase + column + 32) + 200] + 1 ≤
        auxUnit := by
    rw [auxUnitEq]
    simpa [encodedListSpace_cons,
      encodedListSpace_nil] using phaseLimitBits
  have offsetUnitLeAux :
      intOffsetUnit amount rowCode ≤ auxUnit := by
    rw [auxUnitEq]
    simpa [intOffsetUnit, encodedListSpace_cons,
      encodedListSpace_nil] using offsetLimitBits
  have addUnitLeAux :
      encodedListSpace [2 * (x + x) + 4] + 1 ≤ auxUnit := by
    rw [auxUnitEq]
    simpa [encodedListSpace_cons,
      encodedListSpace_nil] using addLimitBits

  have phaseLocal :=
    packedColumnPhaseCost_le_linear period phase column
  have phaseCostBound :
      packedColumnPhaseCost period phase column ≤
        10000000000000000 * scaledUnit :=
    phaseLocal.trans
      (Nat.mul_le_mul_left _
        (phaseUnitLeAux.trans auxLeScaled))
  have offsetLocal :=
    intOffsetCost_le_linear verticalOffset rowCode
  have offsetCostBound :
      intOffsetCost verticalOffset rowCode ≤
        10000000000 * scaledUnit := by
    have enlarged := offsetLocal.trans
      (Nat.mul_le_mul_left (10000000000 * (amount + 1))
        (offsetUnitLeAux.trans auxLeUnit))
    simpa [amount, scaledUnit, Nat.mul_assoc] using enlarged
  have addLocal := natAddCost_le_linear x x
  have addCostBound :
      natAddCost x x ≤ 100000000 * scaledUnit :=
    addLocal.trans
      (Nat.mul_le_mul_left _
        (addUnitLeAux.trans auxLeScaled))
  have pairLocal := natPairCost_le_linear (2 * x) yCode
  have pairCostBound :
      natPairCost (2 * x) yCode ≤
        10000000000000000000000000000000000000000 *
          scaledUnit := by
    exact pairLocal.trans
      (Nat.mul_le_mul_left _ pairLeScaled)

  have auxLengthLeScaled :
      (Computability.encodeNat auxLimit).length ≤ scaledUnit := by
    rw [auxUnitEq] at auxLeScaled
    simp only [encodedListSpace_cons,
      encodedListSpace_nil] at auxLeScaled
    omega
  have periodBitsScaled := periodBits.trans auxLengthLeScaled
  have phaseBitsScaled := phaseBits.trans auxLengthLeScaled
  have columnBitsScaled := columnBits.trans auxLengthLeScaled
  have rowBitsScaled := rowBits.trans auxLengthLeScaled
  have xBitsScaled := xBits.trans auxLengthLeScaled
  have doubleXBitsScaled := doubleXBits.trans auxLengthLeScaled
  have yBitsScaled := yBits.trans auxLengthLeScaled
  have periodSuccBitsScaled := periodSuccBits.trans auxLengthLeScaled
  have phaseSuccBitsScaled := phaseSuccBits.trans auxLengthLeScaled
  have columnSuccBitsScaled := columnSuccBits.trans auxLengthLeScaled
  have rowSuccBitsScaled := rowSuccBits.trans auxLengthLeScaled
  have xSuccBitsScaled := xSuccBits.trans auxLengthLeScaled
  have doubleXSuccBitsScaled :=
    doubleXSuccBits.trans auxLengthLeScaled
  have ySuccBitsScaled := ySuccBits.trans auxLengthLeScaled
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl

  simp only [packedTargetCellCost,
    packedTargetCellArgumentsCost,
    packedTargetXCost, packedTargetXArgumentsCost,
    packedTargetColumnPhaseCost,
    packedTargetColumnArgumentsCost,
    packedTargetColumnArgumentsTailCost,
    packedTargetYCost]
  simp [prependCost, getCost, dropCost, headCost,
    idCost, nilCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    x, yCode, numerator, zeroBits] at *
  omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
