import LeanTrominoes.PartrecFrontierIndexDecode
import LeanTrominoes.PartrecDivisionSpace

/-!
# Evaluator-space certificate for streaming frontier decoding

The two frontier indices are divided by the period into fixed-width word and
phase fields.  Each subsequent assignment step divides two retained words by
nine.  All subprograms use the fitted quotient/remainder evaluator and direct
native-list projections; no encoded assignment list is constructed.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def frontierIndexArgumentsAtCost
    (indexField : Nat) (values : List Nat) : Nat :=
  prependCost values
    [values[indexField]?.getD 0]
    [values[0]?.getD 0]
    (getCost indexField values)
    (getCost 0 values)

theorem frontierIndexArgumentsAt
    (indexField : Nat) (values : List Nat) :
    EvaluatorCodeFits
      (Code.frontierIndexArgumentsAtCode indexField)
      values
      [values[indexField]?.getD 0,
        values[0]?.getD 0]
      (frontierIndexArgumentsAtCost indexField values) := by
  simpa [Code.frontierIndexArgumentsAtCode,
    frontierIndexArgumentsAtCost, prependCost] using
    prepend (get indexField values) (get 0 values)

def frontierIndexViewAtCost
    (indexField : Nat) (values : List Nat) : Nat :=
  divisionSpaceBound
      (values[indexField]?.getD 0)
      (values[0]?.getD 0) +
    frontierIndexArgumentsAtCost indexField values

theorem frontierIndexViewAt
    (indexField : Nat) (values : List Nat) :
    EvaluatorCodeFits
      (Code.frontierIndexViewAtCode indexField)
      values
      [values[indexField]?.getD 0 /
          values[0]?.getD 0,
        values[indexField]?.getD 0 %
          values[0]?.getD 0]
      (frontierIndexViewAtCost indexField values) := by
  simpa [Code.frontierIndexViewAtCode,
    frontierIndexViewAtCost] using
    comp
      (division
        (values[indexField]?.getD 0)
        (values[0]?.getD 0))
      (frontierIndexArgumentsAt indexField values)

def frontierIndexFieldAtCost
    (indexField outputField : Nat)
    (values : List Nat) : Nat :=
  getCost outputField
      [values[indexField]?.getD 0 /
          values[0]?.getD 0,
        values[indexField]?.getD 0 %
          values[0]?.getD 0] +
    frontierIndexViewAtCost indexField values

theorem frontierIndexFieldAt
    (indexField outputField : Nat)
    (values : List Nat) :
    EvaluatorCodeFits
      (Code.frontierIndexFieldAtCode
        indexField outputField)
      values
      [[values[indexField]?.getD 0 /
            values[0]?.getD 0,
          values[indexField]?.getD 0 %
            values[0]?.getD 0][outputField]?.getD 0]
      (frontierIndexFieldAtCost
        indexField outputField values) := by
  simpa [Code.frontierIndexFieldAtCode,
    frontierIndexFieldAtCost] using
    comp
      (get outputField
        [values[indexField]?.getD 0 /
            values[0]?.getD 0,
          values[indexField]?.getD 0 %
            values[0]?.getD 0])
      (frontierIndexViewAt indexField values)

def frontierPairLastCost
    (period first last : Nat) : Nat :=
  let values := [period, first, last]
  prependCost values [last / period] [last % period]
    (frontierIndexFieldAtCost 2 0 values)
    (frontierIndexFieldAtCost 2 1 values)

theorem frontierPairLast
    (period first last : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.frontierIndexFieldAtCode 2 0)
        (Code.frontierIndexFieldAtCode 2 1))
      [period, first, last]
      [last / period, last % period]
      (frontierPairLastCost period first last) := by
  simpa [frontierPairLastCost, prependCost] using
    prepend
      (frontierIndexFieldAt 2 0 [period, first, last])
      (frontierIndexFieldAt 2 1 [period, first, last])

def frontierPairFirstPhaseCost
    (period first last : Nat) : Nat :=
  let values := [period, first, last]
  prependCost values [first % period]
    [last / period, last % period]
    (frontierIndexFieldAtCost 1 1 values)
    (frontierPairLastCost period first last)

theorem frontierPairFirstPhase
    (period first last : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.frontierIndexFieldAtCode 1 1)
        (Code.prepend
          (Code.frontierIndexFieldAtCode 2 0)
          (Code.frontierIndexFieldAtCode 2 1)))
      [period, first, last]
      [first % period, last / period, last % period]
      (frontierPairFirstPhaseCost period first last) := by
  simpa [frontierPairFirstPhaseCost, prependCost] using
    prepend
      (frontierIndexFieldAt 1 1 [period, first, last])
      (frontierPairLast period first last)

def frontierPairViewCost
    (period first last : Nat) : Nat :=
  let values := [period, first, last]
  prependCost values [first / period]
    [first % period, last / period, last % period]
    (frontierIndexFieldAtCost 1 0 values)
    (frontierPairFirstPhaseCost period first last)

theorem frontierPairView
    (period first last : Nat) :
    EvaluatorCodeFits Code.frontierPairViewCode
      [period, first, last]
      [first / period, first % period,
        last / period, last % period]
      (frontierPairViewCost period first last) := by
  simpa [Code.frontierPairViewCode,
    frontierPairViewCost, prependCost] using
    prepend
      (frontierIndexFieldAt 1 0 [period, first, last])
      (frontierPairFirstPhase period first last)

/-- One arithmetic envelope for both quotient/remainder decodings in a
frontier-index pair. -/
def frontierPairPolynomialSpaceLimit
    (period first last : Nat) : Nat :=
  16 * (period + first + last + 20) + 100

/-- Native encoded-list unit for the decoded frontier pair. -/
def frontierPairPolynomialSpaceUnit
    (period first last : Nat) : Nat :=
  encodedListSpace
    [frontierPairPolynomialSpaceLimit period first last] + 1

set_option maxHeartbeats 1200000 in
/-- Dividing two frontier indices by the period and assembling their four
fields uses workspace linear in the native binary input lengths. -/
theorem frontierPairViewCost_le_linear
    (period first last : Nat) :
    frontierPairViewCost period first last ≤
      1000000000000000000000000000000 *
        frontierPairPolynomialSpaceUnit period first last := by
  let limit := frontierPairPolynomialSpaceLimit period first last
  let unit := frontierPairPolynomialSpaceUnit period first last
  have periodBound : period ≤ limit := by
    simp only [limit, frontierPairPolynomialSpaceLimit]
    omega
  have firstBound : first ≤ limit := by
    simp only [limit, frontierPairPolynomialSpaceLimit]
    omega
  have lastBound : last ≤ limit := by
    simp only [limit, frontierPairPolynomialSpaceLimit]
    omega
  have firstDivisionBound : 8 * (first + period) + 16 ≤ limit := by
    simp only [limit, frontierPairPolynomialSpaceLimit]
    omega
  have lastDivisionBound : 8 * (last + period) + 16 ≤ limit := by
    simp only [limit, frontierPairPolynomialSpaceLimit]
    omega
  have firstQuotientBound : first / period ≤ limit :=
    (Nat.div_le_self first period).trans firstBound
  have firstRemainderBound : first % period ≤ limit :=
    (Nat.mod_le first period).trans firstBound
  have lastQuotientBound : last / period ≤ limit :=
    (Nat.div_le_self last period).trans lastBound
  have lastRemainderBound : last % period ≤ limit :=
    (Nat.mod_le last period).trans lastBound
  have periodBits := encodeNat_length_mono periodBound
  have firstBits := encodeNat_length_mono firstBound
  have lastBits := encodeNat_length_mono lastBound
  have firstDivisionBits := encodeNat_length_mono firstDivisionBound
  have lastDivisionBits := encodeNat_length_mono lastDivisionBound
  have firstQuotientBits := encodeNat_length_mono firstQuotientBound
  have firstRemainderBits := encodeNat_length_mono firstRemainderBound
  have lastQuotientBits := encodeNat_length_mono lastQuotientBound
  have lastRemainderBits := encodeNat_length_mono lastRemainderBound
  have periodSuccBits := encodeNat_length_mono
    (show period + 1 ≤ limit by
      simp only [limit, frontierPairPolynomialSpaceLimit]
      omega)
  have firstSuccBits := encodeNat_length_mono
    (show first + 1 ≤ limit by
      simp only [limit, frontierPairPolynomialSpaceLimit]
      omega)
  have lastSuccBits := encodeNat_length_mono
    (show last + 1 ≤ limit by
      simp only [limit, frontierPairPolynomialSpaceLimit]
      omega)
  have firstQuotientSuccBits := encodeNat_length_mono
    (show first / period + 1 ≤ limit by
      have raw := Nat.div_le_self first period
      simp only [limit, frontierPairPolynomialSpaceLimit]
      omega)
  have firstRemainderSuccBits := encodeNat_length_mono
    (show first % period + 1 ≤ limit by
      have raw := Nat.mod_le first period
      simp only [limit, frontierPairPolynomialSpaceLimit]
      omega)
  have lastQuotientSuccBits := encodeNat_length_mono
    (show last / period + 1 ≤ limit by
      have raw := Nat.div_le_self last period
      simp only [limit, frontierPairPolynomialSpaceLimit]
      omega)
  have lastRemainderSuccBits := encodeNat_length_mono
    (show last % period + 1 ≤ limit by
      have raw := Nat.mod_le last period
      simp only [limit, frontierPairPolynomialSpaceLimit]
      omega)
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, frontierPairPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [frontierPairViewCost, frontierPairFirstPhaseCost,
    frontierPairLastCost, frontierIndexFieldAtCost,
    frontierIndexViewAtCost, frontierIndexArgumentsAtCost,
    divisionSpaceBound, prependCost, getCost, dropCost,
    headCost, idCost, nilCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil, zeroBits]
  clear * - periodBits firstBits lastBits
    firstDivisionBits lastDivisionBits
    firstQuotientBits firstRemainderBits
    lastQuotientBits lastRemainderBits
    periodSuccBits firstSuccBits lastSuccBits
    firstQuotientSuccBits firstRemainderSuccBits
    lastQuotientSuccBits lastRemainderSuccBits unitEq
  omega

def assignmentWordStepArgumentsAtCost
    (wordField : Nat) (values : List Nat) : Nat :=
  prependCost values
    [values[wordField]?.getD 0] [9]
    (getCost wordField values)
    (numeralCost 9 values)

theorem assignmentWordStepArgumentsAt
    (wordField : Nat) (values : List Nat) :
    EvaluatorCodeFits
      (Code.assignmentWordStepArgumentsAtCode wordField)
      values [values[wordField]?.getD 0, 9]
      (assignmentWordStepArgumentsAtCost
        wordField values) := by
  simpa [Code.assignmentWordStepArgumentsAtCode,
    assignmentWordStepArgumentsAtCost, prependCost] using
    prepend (get wordField values) (numeral 9 values)

def assignmentWordStepAtCost
    (wordField : Nat) (values : List Nat) : Nat :=
  divisionSpaceBound (values[wordField]?.getD 0) 9 +
    assignmentWordStepArgumentsAtCost wordField values

theorem assignmentWordStepAt
    (wordField : Nat) (values : List Nat) :
    EvaluatorCodeFits
      (Code.assignmentWordStepAtCode wordField)
      values
      [values[wordField]?.getD 0 / 9,
        values[wordField]?.getD 0 % 9]
      (assignmentWordStepAtCost wordField values) := by
  simpa [Code.assignmentWordStepAtCode,
    assignmentWordStepAtCost] using
    comp
      (division (values[wordField]?.getD 0) 9)
      (assignmentWordStepArgumentsAt wordField values)

def assignmentWordStepFieldAtCost
    (wordField outputField : Nat)
    (values : List Nat) : Nat :=
  getCost outputField
      [values[wordField]?.getD 0 / 9,
        values[wordField]?.getD 0 % 9] +
    assignmentWordStepAtCost wordField values

theorem assignmentWordStepFieldAt
    (wordField outputField : Nat)
    (values : List Nat) :
    EvaluatorCodeFits
      (Code.assignmentWordStepFieldAtCode
        wordField outputField)
      values
      [[values[wordField]?.getD 0 / 9,
          values[wordField]?.getD 0 % 9][outputField]?.getD 0]
      (assignmentWordStepFieldAtCost
        wordField outputField values) := by
  simpa [Code.assignmentWordStepFieldAtCode,
    assignmentWordStepFieldAtCost] using
    comp
      (get outputField
        [values[wordField]?.getD 0 / 9,
          values[wordField]?.getD 0 % 9])
      (assignmentWordStepAt wordField values)

def assignmentWordPairLastCost
    (firstWord lastWord : Nat) : Nat :=
  let values := [firstWord, lastWord]
  prependCost values [lastWord / 9] [lastWord % 9]
    (assignmentWordStepFieldAtCost 1 0 values)
    (assignmentWordStepFieldAtCost 1 1 values)

theorem assignmentWordPairLast
    (firstWord lastWord : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.assignmentWordStepFieldAtCode 1 0)
        (Code.assignmentWordStepFieldAtCode 1 1))
      [firstWord, lastWord]
      [lastWord / 9, lastWord % 9]
      (assignmentWordPairLastCost firstWord lastWord) := by
  simpa [assignmentWordPairLastCost, prependCost] using
    prepend
      (assignmentWordStepFieldAt 1 0 [firstWord, lastWord])
      (assignmentWordStepFieldAt 1 1 [firstWord, lastWord])

def assignmentWordPairFirstDigitCost
    (firstWord lastWord : Nat) : Nat :=
  let values := [firstWord, lastWord]
  prependCost values [firstWord % 9]
    [lastWord / 9, lastWord % 9]
    (assignmentWordStepFieldAtCost 0 1 values)
    (assignmentWordPairLastCost firstWord lastWord)

theorem assignmentWordPairFirstDigit
    (firstWord lastWord : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.assignmentWordStepFieldAtCode 0 1)
        (Code.prepend
          (Code.assignmentWordStepFieldAtCode 1 0)
          (Code.assignmentWordStepFieldAtCode 1 1)))
      [firstWord, lastWord]
      [firstWord % 9, lastWord / 9, lastWord % 9]
      (assignmentWordPairFirstDigitCost
        firstWord lastWord) := by
  simpa [assignmentWordPairFirstDigitCost, prependCost] using
    prepend
      (assignmentWordStepFieldAt 0 1 [firstWord, lastWord])
      (assignmentWordPairLast firstWord lastWord)

def assignmentWordPairStepCost
    (firstWord lastWord : Nat) : Nat :=
  let values := [firstWord, lastWord]
  prependCost values [firstWord / 9]
    [firstWord % 9, lastWord / 9, lastWord % 9]
    (assignmentWordStepFieldAtCost 0 0 values)
    (assignmentWordPairFirstDigitCost firstWord lastWord)

theorem assignmentWordPairStep
    (firstWord lastWord : Nat) :
    EvaluatorCodeFits Code.assignmentWordPairStepCode
      [firstWord, lastWord]
      [firstWord / 9, firstWord % 9,
        lastWord / 9, lastWord % 9]
      (assignmentWordPairStepCost
        firstWord lastWord) := by
  simpa [Code.assignmentWordPairStepCode,
    assignmentWordPairStepCost, prependCost] using
    prepend
      (assignmentWordStepFieldAt 0 0 [firstWord, lastWord])
      (assignmentWordPairFirstDigit firstWord lastWord)

end EvaluatorCodeFits

end PartrecToTM2
end Turing
