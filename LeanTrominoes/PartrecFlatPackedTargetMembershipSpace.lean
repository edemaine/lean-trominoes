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

end EvaluatorCodeFits
end PartrecToTM2
end Turing
