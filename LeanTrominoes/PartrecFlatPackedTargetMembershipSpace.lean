import LeanTrominoes.PartrecFlatPackedAssignmentAtBound
import LeanTrominoes.PartrecFlatPackedTargetMembership
import LeanTrominoes.PartrecPackedTargetCellSpace

/-!
# Evaluator-space certificate for flat packed target membership

The target coordinates are computed from the fixed header, then inserted into
the public native-field five-column lookup input while retaining the motif
coordinate suffix.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

private def flatPackedTargetMembershipValues
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : List Nat :=
  [period, phase, motif.length, Encodable.encode row, word] ++
    motif.flatMap PeriodicStripFlatEncoding.cellFields

def flatPackedTargetArgumentsCost
    (column : WindowColumn) (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  let values := flatPackedTargetMembershipValues period phase motif row word
  let rest3 := prependCost values [column.val] [Encodable.encode row]
    (numeralCost column.val values) (getCost 3 values)
  let rest1 := prependCost values [phase] [column.val, Encodable.encode row]
    (getCost 1 values) rest3
  prependCost values [period] [phase, column.val, Encodable.encode row]
    (getCost 0 values) rest1

theorem flatPackedTargetArguments
    (column : WindowColumn) (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    EvaluatorCodeFits (Code.flatPackedTargetArgumentsCode column)
      (flatPackedTargetMembershipValues period phase motif row word)
      [period, phase, column.val, Encodable.encode row]
      (flatPackedTargetArgumentsCost column period phase motif row word) := by
  let values := flatPackedTargetMembershipValues period phase motif row word
  have rest3 := prepend (numeral column.val values) (get 3 values)
  have rest1 := prepend (get 1 values) rest3
  have result := prepend (get 0 values) rest1
  simpa [Code.flatPackedTargetArgumentsCode,
    flatPackedTargetArgumentsCost, flatPackedTargetMembershipValues,
    prependCost, values] using result

def flatPackedTargetXCost
    (column : WindowColumn) (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  packedTargetXCost period phase column.val (Encodable.encode row) +
    flatPackedTargetArgumentsCost column period phase motif row word

theorem flatPackedTargetX
    (column : WindowColumn) (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column.val % period
    EvaluatorCodeFits (Code.flatPackedTargetXCode column)
      (flatPackedTargetMembershipValues period phase motif row word)
      [2 * x]
      (flatPackedTargetXCost column period phase motif row word) := by
  simp only
  simpa [Code.flatPackedTargetXCode, flatPackedTargetXCost] using
    comp (packedTargetX period phase column.val (Encodable.encode row))
      (flatPackedTargetArguments column period phase motif row word)

def flatPackedTargetYCost
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  packedTargetYCost verticalOffset period phase column.val
      (Encodable.encode row) +
    flatPackedTargetArgumentsCost column period phase motif row word

theorem flatPackedTargetY
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    EvaluatorCodeFits (Code.flatPackedTargetYCode column verticalOffset)
      (flatPackedTargetMembershipValues period phase motif row word)
      [Encodable.encode (row + verticalOffset)]
      (flatPackedTargetYCost column verticalOffset period phase motif row
        word) := by
  simpa [Code.flatPackedTargetYCode, flatPackedTargetYCost] using
    comp
      (packedTargetY verticalOffset period phase column.val
        (Encodable.encode row))
      (flatPackedTargetArguments column period phase motif row word)

def flatPackedTargetMembershipLookupArgumentsCost
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  let values := flatPackedTargetMembershipValues period phase motif row word
  let x := Code.packedColumnPhaseNumerator period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  let rest5 := prependCost values [word] coordinates
    (getCost 4 values) (dropCost 5 values)
  let restY := prependCost values [Encodable.encode target.2]
    (word :: coordinates)
    (flatPackedTargetYCost column verticalOffset period phase motif row word)
    rest5
  let restX := prependCost values [2 * x]
    (Encodable.encode target.2 :: word :: coordinates)
    (flatPackedTargetXCost column period phase motif row word) restY
  let restColumn := prependCost values [column.val]
    (2 * x :: Encodable.encode target.2 :: word ::
      coordinates) (numeralCost column.val values) restX
  prependCost values [motif.length]
    (column.val :: 2 * x ::
      Encodable.encode target.2 :: word :: coordinates)
    (getCost 2 values) restColumn

theorem flatPackedTargetMembershipLookupArguments
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column.val % period
    let target : Cell := (Int.ofNat x, row + verticalOffset)
    EvaluatorCodeFits
      (Code.flatPackedTargetMembershipLookupArgumentsCode column
        verticalOffset)
      (flatPackedTargetMembershipValues period phase motif row word)
      ([motif.length, column.val, 2 * x,
          Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatPackedTargetMembershipLookupArgumentsCost column verticalOffset
        period phase motif row word) := by
  simp only
  let values := flatPackedTargetMembershipValues period phase motif row word
  have rest5 := prepend (get 4 values) (drop 5 values)
  have restY := prepend
    (flatPackedTargetY column verticalOffset period phase motif row word) rest5
  have restX := prepend
    (flatPackedTargetX column period phase motif row word) restY
  have restColumn := prepend (numeral column.val values) restX
  have result := prepend (get 2 values) restColumn
  simpa [Code.flatPackedTargetMembershipLookupArgumentsCode,
    flatPackedTargetMembershipLookupArgumentsCost,
    flatPackedTargetMembershipValues, prependCost, values,
    IntEncoding.encode_ofNat] using result

def flatPackedTargetMembershipLookupCost
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  let x := Code.packedColumnPhaseNumerator period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  flatPackedAssignmentLookupCost motif column.val target word +
    flatPackedTargetMembershipLookupArgumentsCost column verticalOffset
      period phase motif row word

theorem flatPackedTargetMembershipLookup
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column.val % period
    let target : Cell := (Int.ofNat x, row + verticalOffset)
    let outcome := Code.packedAssignmentLookupOutcome motif column.val target
      word
    EvaluatorCodeFits
      (Code.flatPackedAssignmentLookupCode.comp
        (Code.flatPackedTargetMembershipLookupArgumentsCode column
          verticalOffset))
      (flatPackedTargetMembershipValues period phase motif row word)
      [outcome.2.1, outcome.2.2.toNat]
      (flatPackedTargetMembershipLookupCost column verticalOffset period phase
        motif row word) := by
  simp only
  let x := Code.packedColumnPhaseNumerator period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  simpa [flatPackedTargetMembershipLookupCost, x, target] using
    comp (flatPackedAssignmentLookup motif column.val target word)
      (flatPackedTargetMembershipLookupArguments column verticalOffset period
        phase motif row word)

def flatPackedTargetMembershipCost
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  let x := Code.packedColumnPhaseNumerator period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  let outcome := Code.packedAssignmentLookupOutcome motif column.val target
    word
  getCost 1 [outcome.2.1, outcome.2.2.toNat] +
    flatPackedTargetMembershipLookupCost column verticalOffset period phase
      motif row word

/-- Exact fitted execution of the native-field target-membership leaf. -/
theorem flatPackedTargetMembership
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column.val % period
    let target : Cell := (Int.ofNat x, row + verticalOffset)
    let outcome := Code.packedAssignmentLookupOutcome motif column.val target
      word
    EvaluatorCodeFits (Code.flatPackedTargetMembershipCode column
        verticalOffset)
      (flatPackedTargetMembershipValues period phase motif row word)
      [outcome.2.2.toNat]
      (flatPackedTargetMembershipCost column verticalOffset period phase motif
        row word) := by
  simp only
  let x := Code.packedColumnPhaseNumerator period phase column.val % period
  let target : Cell := (Int.ofNat x, row + verticalOffset)
  let outcome := Code.packedAssignmentLookupOutcome motif column.val target
    word
  simpa [Code.flatPackedTargetMembershipCode,
    flatPackedTargetMembershipCost, outcome, x, target] using
    comp (get 1 [outcome.2.1, outcome.2.2.toNat])
      (flatPackedTargetMembershipLookup column verticalOffset period phase
        motif row word)

/-! ## Native-field bounds -/

/-- The public input footprint, augmented only by the two fixed program
constants (column and vertical offset). -/
def flatPackedTargetMembershipNativeInputSpace
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  encodedListSpace
      (flatPackedTargetMembershipValues period phase motif row word) +
    encodedListSpace [column.val] +
    encodedListSpace [intOffsetAmount verticalOffset] + 10

def flatPackedTargetConstructorBudget
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) : Nat :=
  1000000000000000000000000000000000000000000000000000000000000 *
    (intOffsetAmount verticalOffset + 1) *
    flatPackedTargetMembershipNativeInputSpace column verticalOffset period
      phase motif row word

theorem flatPackedTargetMembershipNativeInputSpacePositive
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    10 ≤ flatPackedTargetMembershipNativeInputSpace column verticalOffset
      period phase motif row word := by
  simp [flatPackedTargetMembershipNativeInputSpace]

set_option maxRecDepth 10000 in
theorem flatPackedTargetArgumentsCost_le_native
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    flatPackedTargetArgumentsCost column period phase motif row word ≤
      1000000 * flatPackedTargetMembershipNativeInputSpace column
        verticalOffset period phase motif row word := by
  let values := flatPackedTargetMembershipValues period phase motif row word
  let unit := flatPackedTargetMembershipNativeInputSpace column verticalOffset
    period phase motif row word
  let localBudget := 100000 * unit
  have unitPositive : 10 ≤ unit := by
    simpa [unit] using flatPackedTargetMembershipNativeInputSpacePositive
      column verticalOffset period phase motif row word
  have valuesBound : encodedListSpace values ≤ unit := by
    simp [unit, flatPackedTargetMembershipNativeInputSpace, values]
    omega
  have columnSpace : encodedListSpace [column.val] ≤ unit := by
    simp [unit, flatPackedTargetMembershipNativeInputSpace]
    omega
  have periodSpace : encodedListSpace [period] ≤ unit := by
    simp [unit, flatPackedTargetMembershipNativeInputSpace,
      flatPackedTargetMembershipValues, encodedListSpace_cons]
    omega
  have phaseSpace : encodedListSpace [phase] ≤ unit := by
    simp [unit, flatPackedTargetMembershipNativeInputSpace,
      flatPackedTargetMembershipValues, encodedListSpace_cons]
    omega
  have rowSpace : encodedListSpace [Encodable.encode row] ≤ unit := by
    simp [unit, flatPackedTargetMembershipNativeInputSpace,
      flatPackedTargetMembershipValues, encodedListSpace_cons]
    omega
  have out3Space :
      encodedListSpace [column.val, Encodable.encode row] ≤ unit := by
    simp [unit, flatPackedTargetMembershipNativeInputSpace,
      flatPackedTargetMembershipValues, encodedListSpace_cons]
    omega
  have out1Space :
      encodedListSpace [phase, column.val, Encodable.encode row] ≤ unit := by
    simp [unit, flatPackedTargetMembershipNativeInputSpace,
      flatPackedTargetMembershipValues, encodedListSpace_cons]
    omega
  have finalSpace :
      encodedListSpace [period, phase, column.val, Encodable.encode row] ≤
        unit := by
    simp [unit, flatPackedTargetMembershipNativeInputSpace,
      flatPackedTargetMembershipValues, encodedListSpace_cons]
    omega
  have get0Raw := listCodeGetCost_le_linear 0 values
  have get1Raw := listCodeGetCost_le_linear 1 values
  have get3Raw := listCodeGetCost_le_linear 3 values
  have get0 : getCost 0 values ≤ localBudget :=
    get0Raw.trans (by simp [localBudget]; omega)
  have get1 : getCost 1 values ≤ localBudget :=
    get1Raw.trans (by simp [localBudget]; omega)
  have get3 : getCost 3 values ≤ localBudget :=
    get3Raw.trans (by simp [localBudget]; omega)
  have zeroRaw := listCodeZeroCost_le_linear values
  have addSmall : addConstCost column.val [0] ≤ 1000000 := by
    fin_cases column <;> native_decide
  have numeral : numeralCost column.val values ≤ 2 * localBudget := by
    simp only [numeralCost]
    have zero : zeroCost values ≤ localBudget :=
      zeroRaw.trans (by simp [localBudget]; omega)
    omega
  let cost3 := prependCost values [column.val] [Encodable.encode row]
    (numeralCost column.val values) (getCost 3 values)
  let cost1 := prependCost values [phase]
    [column.val, Encodable.encode row] (getCost 1 values) cost3
  let cost0 := prependCost values [period]
    [phase, column.val, Encodable.encode row] (getCost 0 values) cost1
  have estimate3 := listCodePrependCost_le_of values [column.val]
    [Encodable.encode row] (numeralCost column.val values) (getCost 3 values)
    unit valuesBound columnSpace out3Space
  have bound3 : cost3 ≤ 4 * localBudget := by
    simp only [cost3]
    simp [localBudget]
    omega
  have estimate1 := listCodePrependCost_le_of values [phase]
    [column.val, Encodable.encode row] (getCost 1 values) cost3 unit
    valuesBound phaseSpace out1Space
  have bound1 : cost1 ≤ 6 * localBudget := by
    simp only [cost1]
    simp [localBudget]
    omega
  have estimate0 := listCodePrependCost_le_of values [period]
    [phase, column.val, Encodable.encode row] (getCost 0 values) cost1 unit
    valuesBound periodSpace finalSpace
  have bound0 : cost0 ≤ 10 * localBudget := by
    simp only [cost0]
    simp [localBudget]
    omega
  change cost0 ≤ 1000000 * unit
  calc
    cost0 ≤ 10 * localBudget := bound0
    _ = 1000000 * unit := by simp only [localBudget]; ring

theorem flatPackedTargetCoordinateCosts_le_constructor
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell)
    (row : Int) (word : Nat) :
    flatPackedTargetXCost column period phase motif row word ≤
        flatPackedTargetConstructorBudget column verticalOffset period phase
          motif row word ∧
      flatPackedTargetYCost column verticalOffset period phase motif row word ≤
        flatPackedTargetConstructorBudget column verticalOffset period phase
          motif row word := by
  let rowCode := Encodable.encode row
  let unit := flatPackedTargetMembershipNativeInputSpace column verticalOffset
    period phase motif row word
  let constructorBudget := flatPackedTargetConstructorBudget column verticalOffset
    period phase motif row word
  have unitPositive : 10 ≤ unit := by
    simpa [unit] using flatPackedTargetMembershipNativeInputSpacePositive
      column verticalOffset period phase motif row word
  have bitsToUnit :
      (Computability.encodeNat period).length +
          (Computability.encodeNat phase).length +
          (Computability.encodeNat column.val).length +
          (Computability.encodeNat rowCode).length +
          (Computability.encodeNat
            (intOffsetAmount verticalOffset)).length + 1 ≤ unit := by
    simp [unit, flatPackedTargetMembershipNativeInputSpace,
      flatPackedTargetMembershipValues, rowCode, encodedListSpace_cons]
    omega
  have cellUnit := packedTargetCellUnit_le_linear verticalOffset period phase
    column.val rowCode
  have cellUnitBound :
      packedTargetCellUnit verticalOffset period phase column.val rowCode ≤
        100000 * unit := cellUnit.trans (Nat.mul_le_mul_left _ bitsToUnit)
  have whole := packedTargetCellCost_le_linear verticalOffset period phase
    column.val rowCode
  have wholeBound :
      packedTargetCellCost verticalOffset period phase column.val rowCode ≤
        100000000000000000000000000000000000000000000000000 *
          (intOffsetAmount verticalOffset + 1) * unit := by
    calc
      packedTargetCellCost verticalOffset period phase column.val rowCode ≤
          1000000000000000000000000000000000000000000000 *
            (intOffsetAmount verticalOffset + 1) *
            packedTargetCellUnit verticalOffset period phase column.val
              rowCode := whole
      _ ≤ 1000000000000000000000000000000000000000000000 *
            (intOffsetAmount verticalOffset + 1) * (100000 * unit) := by
          gcongr
      _ = 100000000000000000000000000000000000000000000000000 *
            (intOffsetAmount verticalOffset + 1) * unit := by ring
  have xPart :
      packedTargetXCost period phase column.val rowCode ≤
        packedTargetCellCost verticalOffset period phase column.val rowCode := by
    simp [packedTargetCellCost, packedTargetCellArgumentsCost, prependCost]
    omega
  have yPart :
      packedTargetYCost verticalOffset period phase column.val rowCode ≤
        packedTargetCellCost verticalOffset period phase column.val rowCode := by
    simp [packedTargetCellCost, packedTargetCellArgumentsCost, prependCost]
    omega
  have adapter := flatPackedTargetArgumentsCost_le_native column verticalOffset
    period phase motif row word
  constructor
  · change packedTargetXCost period phase column.val rowCode +
        flatPackedTargetArgumentsCost column period phase motif row word ≤
      constructorBudget
    simp [constructorBudget, flatPackedTargetConstructorBudget]
    nlinarith
  · change packedTargetYCost verticalOffset period phase column.val rowCode +
        flatPackedTargetArgumentsCost column period phase motif row word ≤
      constructorBudget
    simp [constructorBudget, flatPackedTargetConstructorBudget]
    nlinarith

end EvaluatorCodeFits
end PartrecToTM2
end Turing
