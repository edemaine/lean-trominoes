import LeanTrominoes.PartrecDivisionSpace
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecPackedCenterLoopSpace
import LeanTrominoes.PartrecPackedNormalizationAllSpace
import LeanTrominoes.PartrecPackedOverlapLoopSpace
import LeanTrominoes.PartrecPackedTransition

/-!
# Evaluator-space certificate for the packed frontier transition

The exact certificates for normalization, center validity, phase advance, and
overlap are adapted to one six-field input and composed into the complete
packed transition predicate.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

private theorem boolAnd_fit_bool
    {leftCode rightCode : Code} {values : List Nat}
    {leftCost rightCost : Nat}
    (left right : Bool)
    (leftFit : EvaluatorCodeFits leftCode values
      [left.toNat] leftCost)
    (rightFit : EvaluatorCodeFits rightCode values
      [right.toNat] rightCost) :
    EvaluatorCodeFits (Code.boolAnd leftCode rightCode) values
      [(left && right).toNat]
      (boolAndCost values left.toNat right.toNat
        leftCost rightCost) := by
  have combined := boolAnd leftFit rightFit
  cases left <;> cases right <;> simpa using combined

def packedTransitionCurrentArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let restMotifWord := prependCost values
    [Encodable.encode periodicStrip.motif]
    [current.assignmentWord]
    (getCost 2 values) (getCost 3 values)
  let restPhase := prependCost values [current.phase]
    [Encodable.encode periodicStrip.motif, current.assignmentWord]
    (getCost 1 values) restMotifWord
  prependCost values [periodicStrip.period]
    [current.phase, Encodable.encode periodicStrip.motif,
      current.assignmentWord]
    (getCost 0 values) restPhase

theorem packedTransitionCurrentArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionCurrentArgumentsCode
      (Code.packedTransitionInput periodicStrip current next)
      [periodicStrip.period, current.phase,
        Encodable.encode periodicStrip.motif,
        current.assignmentWord]
      (packedTransitionCurrentArgumentsCost
        periodicStrip current next) := by
  let values := Code.packedTransitionInput periodicStrip current next
  have restMotifWord := prepend (get 2 values) (get 3 values)
  have restPhase := prepend (get 1 values) restMotifWord
  have result := prepend (get 0 values) restPhase
  simpa [Code.packedTransitionCurrentArgumentsCode,
    packedTransitionCurrentArgumentsCost,
    Code.packedTransitionInput, prependCost, values] using result

def packedTransitionOverlapArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let words := prependCost values [current.assignmentWord]
    [next.assignmentWord]
    (getCost 3 values) (getCost 5 values)
  prependCost values [Encodable.encode periodicStrip.motif]
    [current.assignmentWord, next.assignmentWord]
    (getCost 2 values) words

theorem packedTransitionOverlapArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionOverlapArgumentsCode
      (Code.packedTransitionInput periodicStrip current next)
      [Encodable.encode periodicStrip.motif,
        current.assignmentWord, next.assignmentWord]
      (packedTransitionOverlapArgumentsCost
        periodicStrip current next) := by
  let values := Code.packedTransitionInput periodicStrip current next
  have words := prepend (get 3 values) (get 5 values)
  have result := prepend (get 2 values) words
  simpa [Code.packedTransitionOverlapArgumentsCode,
    packedTransitionOverlapArgumentsCost,
    Code.packedTransitionInput, prependCost, values] using result

def packedTransitionPhaseDivisionArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let successorCost := succCost [current.phase] + getCost 1 values
  prependCost values [current.phase + 1] [periodicStrip.period]
    successorCost (getCost 0 values)

theorem packedTransitionPhaseDivisionArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      Code.packedTransitionPhaseDivisionArgumentsCode
      (Code.packedTransitionInput periodicStrip current next)
      [current.phase + 1, periodicStrip.period]
      (packedTransitionPhaseDivisionArgumentsCost
        periodicStrip current next) := by
  let values := Code.packedTransitionInput periodicStrip current next
  have successor := comp (succ_named [current.phase]) (get 1 values)
  have result := prepend successor (get 0 values)
  simpa [Code.packedTransitionPhaseDivisionArgumentsCode,
    packedTransitionPhaseDivisionArgumentsCost,
    Code.packedTransitionInput, prependCost, values] using result

def packedTransitionPhaseRemainderCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  getCost 1
      [(current.phase + 1) / periodicStrip.period,
        (current.phase + 1) % periodicStrip.period] +
    (divisionSpaceBound (current.phase + 1) periodicStrip.period +
      packedTransitionPhaseDivisionArgumentsCost
        periodicStrip current next)

theorem packedTransitionPhaseRemainder
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionPhaseRemainderCode
      (Code.packedTransitionInput periodicStrip current next)
      [(current.phase + 1) % periodicStrip.period]
      (packedTransitionPhaseRemainderCost
        periodicStrip current next) := by
  have divided := comp
    (division (current.phase + 1) periodicStrip.period)
    (packedTransitionPhaseDivisionArguments
      periodicStrip current next)
  have projected := comp
    (get 1 [(current.phase + 1) / periodicStrip.period,
      (current.phase + 1) % periodicStrip.period]) divided
  simpa [Code.packedTransitionPhaseRemainderCode,
    packedTransitionPhaseRemainderCost] using projected

def packedTransitionPhaseEqualityArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  prependCost values [next.phase]
    [(current.phase + 1) % periodicStrip.period]
    (getCost 4 values)
    (packedTransitionPhaseRemainderCost
      periodicStrip current next)

theorem packedTransitionPhaseEqualityArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      Code.packedTransitionPhaseEqualityArgumentsCode
      (Code.packedTransitionInput periodicStrip current next)
      [next.phase, (current.phase + 1) % periodicStrip.period]
      (packedTransitionPhaseEqualityArgumentsCost
        periodicStrip current next) := by
  let values := Code.packedTransitionInput periodicStrip current next
  have result := prepend (get 4 values)
    (packedTransitionPhaseRemainder periodicStrip current next)
  simpa [Code.packedTransitionPhaseEqualityArgumentsCode,
    packedTransitionPhaseEqualityArgumentsCost,
    Code.packedTransitionInput, prependCost, values] using result

def packedTransitionPhaseCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  natEqCost next.phase
      ((current.phase + 1) % periodicStrip.period) +
    packedTransitionPhaseEqualityArgumentsCost
      periodicStrip current next

theorem packedTransitionPhase
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    let advances := decide
      (next.phase =
        (current.phase + 1) % periodicStrip.period)
    EvaluatorCodeFits Code.packedTransitionPhaseCode
      (Code.packedTransitionInput periodicStrip current next)
      [advances.toNat]
      (packedTransitionPhaseCost periodicStrip current next) := by
  simp only
  have result := comp
    (natEq next.phase
      ((current.phase + 1) % periodicStrip.period))
    (packedTransitionPhaseEqualityArguments
      periodicStrip current next)
  have tagEq :
      (decide (next.phase =
        (current.phase + 1) % periodicStrip.period)).toNat =
      if next.phase =
        (current.phase + 1) % periodicStrip.period then 1 else 0 := by
    by_cases advances :
        next.phase =
          (current.phase + 1) % periodicStrip.period <;>
      simp [advances]
  rw [tagEq]
  simpa [Code.packedTransitionPhaseCode,
    packedTransitionPhaseCost] using result

/-- One native-number envelope for the six packed-transition fields and the
intermediate phase arithmetic.  The repeated motif terms also make this
envelope large enough to absorb the normalization, center, and overlap
component envelopes below. -/
def packedTransitionPolynomialSpaceLimit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let motifCode := Encodable.encode periodicStrip.motif
  8192 * (periodicStrip.period + current.phase +
    motifCode + motifCode + motifCode + motifCode +
    motifCode + motifCode + motifCode +
    current.assignmentWord + next.phase + next.assignmentWord + 200) + 4000

/-- Native encoded-list workspace unit for the packed transition. -/
def packedTransitionNativeSpaceUnit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  encodedListSpace
    [packedTransitionPolynomialSpaceLimit periodicStrip current next] + 1

private theorem packedTransitionNativeSpaceUnit_eq
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionNativeSpaceUnit periodicStrip current next =
      (Computability.encodeNat
        (packedTransitionPolynomialSpaceLimit
          periodicStrip current next)).length + 2 := by
  simp [packedTransitionNativeSpaceUnit,
    encodedListSpace_cons, encodedListSpace_nil]

private theorem packedTransitionInputSpace_le_nativeUnit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    encodedListSpace
        (Code.packedTransitionInput periodicStrip current next) ≤
      10 * packedTransitionNativeSpaceUnit
        periodicStrip current next := by
  let limit := packedTransitionPolynomialSpaceLimit
    periodicStrip current next
  let unit := packedTransitionNativeSpaceUnit
    periodicStrip current next
  have periodBound : periodicStrip.period ≤ limit := by
    simp only [limit, packedTransitionPolynomialSpaceLimit]
    omega
  have currentPhaseBound : current.phase ≤ limit := by
    simp only [limit, packedTransitionPolynomialSpaceLimit]
    omega
  have motifBound : Encodable.encode periodicStrip.motif ≤ limit := by
    simp only [limit, packedTransitionPolynomialSpaceLimit]
    omega
  have currentWordBound : current.assignmentWord ≤ limit := by
    simp only [limit, packedTransitionPolynomialSpaceLimit]
    omega
  have nextPhaseBound : next.phase ≤ limit := by
    simp only [limit, packedTransitionPolynomialSpaceLimit]
    omega
  have nextWordBound : next.assignmentWord ≤ limit := by
    simp only [limit, packedTransitionPolynomialSpaceLimit]
    omega
  have periodBits := encodeNat_length_mono periodBound
  have currentPhaseBits := encodeNat_length_mono currentPhaseBound
  have motifBits := encodeNat_length_mono motifBound
  have currentWordBits := encodeNat_length_mono currentWordBound
  have nextPhaseBits := encodeNat_length_mono nextPhaseBound
  have nextWordBits := encodeNat_length_mono nextWordBound
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, packedTransitionNativeSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  simp only [Code.packedTransitionInput,
    encodedListSpace_cons, encodedListSpace_nil]
  rw [show packedTransitionNativeSpaceUnit periodicStrip current next =
      unit by rfl, unitEq]
  omega

private theorem packedTransitionInputHeadSpace_le_nativeUnit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    (Computability.encodeNat
        (Code.packedTransitionInput periodicStrip current next).headI).length ≤
      10 * packedTransitionNativeSpaceUnit
        periodicStrip current next := by
  have inputSpace := packedTransitionInputSpace_le_nativeUnit
    periodicStrip current next
  simp [Code.packedTransitionInput] at inputSpace ⊢
  omega

private theorem packedTransitionInputHeadSuccSpace_le_nativeUnit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    (Computability.encodeNat
        ((Code.packedTransitionInput periodicStrip current next).headI + 1)).length ≤
      20 * packedTransitionNativeSpaceUnit
        periodicStrip current next := by
  have headSpace := packedTransitionInputHeadSpace_le_nativeUnit
    periodicStrip current next
  have successor := encodeNat_succ_length_le
    (Code.packedTransitionInput periodicStrip current next).headI
  have successor' :
      (Computability.encodeNat
          ((Code.packedTransitionInput periodicStrip current next).headI + 1)).length ≤
        (Computability.encodeNat
          (Code.packedTransitionInput periodicStrip current next).headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using successor
  have unitPositive :
      1 ≤ packedTransitionNativeSpaceUnit periodicStrip current next := by
    simp [packedTransitionNativeSpaceUnit]
  omega

set_option maxHeartbeats 800000 in
theorem packedTransitionCurrentArgumentsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionCurrentArgumentsCost periodicStrip current next ≤
      1000000 * packedTransitionNativeSpaceUnit
        periodicStrip current next := by
  let limit := packedTransitionPolynomialSpaceLimit
    periodicStrip current next
  let unit := packedTransitionNativeSpaceUnit
    periodicStrip current next
  have periodBits := encodeNat_length_mono
    (show periodicStrip.period ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have currentPhaseBits := encodeNat_length_mono
    (show current.phase ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have motifBits := encodeNat_length_mono
    (show Encodable.encode periodicStrip.motif ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have currentWordBits := encodeNat_length_mono
    (show current.assignmentWord ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have periodSuccBits := encodeNat_length_mono
    (show periodicStrip.period + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have currentPhaseSuccBits := encodeNat_length_mono
    (show current.phase + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have motifSuccBits := encodeNat_length_mono
    (show Encodable.encode periodicStrip.motif + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have currentWordSuccBits := encodeNat_length_mono
    (show current.assignmentWord + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, packedTransitionNativeSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have inputSpace := packedTransitionInputSpace_le_nativeUnit
    periodicStrip current next
  simp only [Code.packedTransitionInput,
    encodedListSpace_cons, encodedListSpace_nil] at inputSpace
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [packedTransitionCurrentArgumentsCost,
    Code.packedTransitionInput, prependCost,
    getCost, dropCost, headCost, idCost,
    nilCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil]
  omega

set_option maxHeartbeats 800000 in
theorem packedTransitionOverlapArgumentsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionOverlapArgumentsCost periodicStrip current next ≤
      1000000 * packedTransitionNativeSpaceUnit
        periodicStrip current next := by
  let limit := packedTransitionPolynomialSpaceLimit
    periodicStrip current next
  let unit := packedTransitionNativeSpaceUnit
    periodicStrip current next
  have motifBits := encodeNat_length_mono
    (show Encodable.encode periodicStrip.motif ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have currentWordBits := encodeNat_length_mono
    (show current.assignmentWord ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have nextWordBits := encodeNat_length_mono
    (show next.assignmentWord ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have motifSuccBits := encodeNat_length_mono
    (show Encodable.encode periodicStrip.motif + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have currentWordSuccBits := encodeNat_length_mono
    (show current.assignmentWord + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have nextWordSuccBits := encodeNat_length_mono
    (show next.assignmentWord + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, packedTransitionNativeSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have inputSpace := packedTransitionInputSpace_le_nativeUnit
    periodicStrip current next
  simp only [Code.packedTransitionInput,
    encodedListSpace_cons, encodedListSpace_nil] at inputSpace
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [packedTransitionOverlapArgumentsCost,
    Code.packedTransitionInput, prependCost,
    getCost, dropCost, headCost, idCost,
    nilCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil]
  omega

set_option maxHeartbeats 800000 in
theorem packedTransitionPhaseDivisionArgumentsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionPhaseDivisionArgumentsCost periodicStrip current next ≤
      1000000 * packedTransitionNativeSpaceUnit
        periodicStrip current next := by
  let limit := packedTransitionPolynomialSpaceLimit
    periodicStrip current next
  let unit := packedTransitionNativeSpaceUnit
    periodicStrip current next
  have periodBits := encodeNat_length_mono
    (show periodicStrip.period ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have currentPhaseBits := encodeNat_length_mono
    (show current.phase ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have currentPhaseSuccBits := encodeNat_length_mono
    (show current.phase + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have periodSuccBits := encodeNat_length_mono
    (show periodicStrip.period + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have currentPhaseSuccSuccBits := encodeNat_length_mono
    (show current.phase + 1 + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, packedTransitionNativeSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have inputSpace := packedTransitionInputSpace_le_nativeUnit
    periodicStrip current next
  simp only [Code.packedTransitionInput,
    encodedListSpace_cons, encodedListSpace_nil] at inputSpace
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [packedTransitionPhaseDivisionArgumentsCost,
    Code.packedTransitionInput, prependCost,
    getCost, dropCost, headCost, idCost,
    nilCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil]
  omega

set_option maxHeartbeats 800000 in
theorem packedTransitionPhaseRemainderCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionPhaseRemainderCost periodicStrip current next ≤
      1000000000000000000 * packedTransitionNativeSpaceUnit
        periodicStrip current next := by
  let limit := packedTransitionPolynomialSpaceLimit
    periodicStrip current next
  let unit := packedTransitionNativeSpaceUnit
    periodicStrip current next
  have divisionBound := divisionUniformCost_le_input
    (current.phase + 1) periodicStrip.period
  have divisionLimit :
      8 * (current.phase + 1 + periodicStrip.period) + 16 ≤ limit := by
    simp only [limit, packedTransitionPolynomialSpaceLimit]
    omega
  have divisionBits := encodeNat_length_mono divisionLimit
  have argumentsBound :=
    packedTransitionPhaseDivisionArgumentsCost_le_linear
      periodicStrip current next
  have remainderBound :
      (current.phase + 1) % periodicStrip.period ≤ limit := by
    exact (Nat.mod_le (current.phase + 1) periodicStrip.period).trans
      (show current.phase + 1 ≤ limit by
        simp only [limit, packedTransitionPolynomialSpaceLimit]
        omega)
  have remainderBits := encodeNat_length_mono remainderBound
  have remainderSuccBits := encodeNat_length_mono
    (show (current.phase + 1) % periodicStrip.period + 1 ≤ limit by
      have raw := Nat.mod_le (current.phase + 1) periodicStrip.period
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have quotientBits := encodeNat_length_mono
    (show (current.phase + 1) / periodicStrip.period ≤ limit by
      exact (Nat.div_le_self (current.phase + 1)
        periodicStrip.period).trans
          (show current.phase + 1 ≤ limit by
            simp only [limit, packedTransitionPolynomialSpaceLimit]
            omega))
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, packedTransitionNativeSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have nativeUnitEq := packedTransitionNativeSpaceUnit_eq
    periodicStrip current next
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [packedTransitionPhaseRemainderCost,
    divisionSpaceBound, encodedListSpace_cons, encodedListSpace_nil,
    getCost, dropCost, headCost, idCost, nilCost,
    tailCost, zeroPrimeCost, succCost]
  simp only [packedTransitionNativeSpaceUnit,
    encodedListSpace_cons, encodedListSpace_nil] at argumentsBound
  clear * - divisionBits argumentsBound remainderBits
    remainderSuccBits quotientBits unitEq nativeUnitEq zeroBits
  omega

set_option maxHeartbeats 800000 in
theorem packedTransitionPhaseEqualityArgumentsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionPhaseEqualityArgumentsCost periodicStrip current next ≤
      10000000000000000000 * packedTransitionNativeSpaceUnit
        periodicStrip current next := by
  let limit := packedTransitionPolynomialSpaceLimit
    periodicStrip current next
  let unit := packedTransitionNativeSpaceUnit
    periodicStrip current next
  have nextPhaseBits := encodeNat_length_mono
    (show next.phase ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have nextPhaseSuccBits := encodeNat_length_mono
    (show next.phase + 1 ≤ limit by
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have remainderBits := encodeNat_length_mono
    (show (current.phase + 1) % periodicStrip.period ≤ limit by
      exact (Nat.mod_le (current.phase + 1) periodicStrip.period).trans
        (show current.phase + 1 ≤ limit by
          simp only [limit, packedTransitionPolynomialSpaceLimit]
          omega))
  have remainderSuccBits := encodeNat_length_mono
    (show (current.phase + 1) % periodicStrip.period + 1 ≤ limit by
      have raw := Nat.mod_le (current.phase + 1) periodicStrip.period
      simp only [limit, packedTransitionPolynomialSpaceLimit]
      omega)
  have remainderCost := packedTransitionPhaseRemainderCost_le_linear
    periodicStrip current next
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, packedTransitionNativeSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have inputSpace := packedTransitionInputSpace_le_nativeUnit
    periodicStrip current next
  simp only [Code.packedTransitionInput,
    encodedListSpace_cons, encodedListSpace_nil] at inputSpace
  have nativeUnitEq := packedTransitionNativeSpaceUnit_eq
    periodicStrip current next
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [packedTransitionPhaseEqualityArgumentsCost,
    Code.packedTransitionInput, prependCost,
    getCost, dropCost, headCost, idCost,
    nilCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil]
  simp only [packedTransitionNativeSpaceUnit,
    encodedListSpace_cons, encodedListSpace_nil] at remainderCost
  omega

set_option maxHeartbeats 1000000 in
theorem packedTransitionPhaseCost_le_polynomialSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionPhaseCost periodicStrip current next ≤
      100000000000000000000000000000000 *
        packedTransitionNativeSpaceUnit periodicStrip current next := by
  let limit := packedTransitionPolynomialSpaceLimit
    periodicStrip current next
  let unit := packedTransitionNativeSpaceUnit
    periodicStrip current next
  have equalityCost := natEqCost_le_linear next.phase
    ((current.phase + 1) % periodicStrip.period)
  have equalityLimit :
      2 * (next.phase +
        (current.phase + 1) % periodicStrip.period) + 4 ≤ limit := by
    have remainderLe := Nat.mod_le
      (current.phase + 1) periodicStrip.period
    simp only [limit, packedTransitionPolynomialSpaceLimit]
    omega
  have equalityBits := encodeNat_length_mono equalityLimit
  have argumentsCost :=
    packedTransitionPhaseEqualityArgumentsCost_le_linear
      periodicStrip current next
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, packedTransitionNativeSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have nativeUnitEq := packedTransitionNativeSpaceUnit_eq
    periodicStrip current next
  simp only [packedTransitionPhaseCost,
    encodedListSpace_cons, encodedListSpace_nil] at equalityCost ⊢
  simp only [packedTransitionNativeSpaceUnit,
    encodedListSpace_cons, encodedListSpace_nil] at argumentsCost
  clear * - equalityCost equalityBits argumentsCost unitEq nativeUnitEq
  omega

def packedTransitionNormalizationCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  packedNormalizationAllCost periodicStrip current +
    packedTransitionCurrentArgumentsCost periodicStrip current next

theorem packedTransitionNormalization
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionNormalizationCode
      (Code.packedTransitionInput periodicStrip current next)
      [(current.isNormalizedBool periodicStrip).toNat]
      (packedTransitionNormalizationCost
        periodicStrip current next) := by
  simpa [Code.packedTransitionNormalizationCode,
    packedTransitionNormalizationCost] using
    comp (packedNormalizationAll periodicStrip current)
      (packedTransitionCurrentArguments periodicStrip current next)

def packedTransitionCenterCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  packedCenterValidCost tromino periodicStrip current +
    packedTransitionCurrentArgumentsCost periodicStrip current next

theorem packedTransitionCenter
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.packedTransitionCenterCode tromino)
      (Code.packedTransitionInput periodicStrip current next)
      [(current.isCenterValidBool tromino periodicStrip).toNat]
      (packedTransitionCenterCost
        tromino periodicStrip current next) := by
  simpa [Code.packedTransitionCenterCode,
    packedTransitionCenterCost] using
    comp (packedCenterValid tromino periodicStrip wellFormed current)
      (packedTransitionCurrentArguments periodicStrip current next)

def packedTransitionOverlapColumnsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  packedOverlapColumnsCost periodicStrip current next +
    packedTransitionOverlapArgumentsCost periodicStrip current next

theorem packedTransitionOverlapColumns
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionOverlapColumnsCode
      (Code.packedTransitionInput periodicStrip current next)
      [((List.finRange 4).all fun column =>
        current.overlapsColumnBool periodicStrip next column).toNat]
      (packedTransitionOverlapColumnsCost
        periodicStrip current next) := by
  simpa [Code.packedTransitionOverlapColumnsCode,
    packedTransitionOverlapColumnsCost] using
    comp (packedOverlapColumns periodicStrip current next)
      (packedTransitionOverlapArguments periodicStrip current next)

def packedTransitionOverlapCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let phase := decide
    (next.phase = (current.phase + 1) % periodicStrip.period)
  let columns := (List.finRange 4).all fun column =>
    current.overlapsColumnBool periodicStrip next column
  boolAndCost values phase.toNat columns.toNat
    (packedTransitionPhaseCost periodicStrip current next)
    (packedTransitionOverlapColumnsCost
      periodicStrip current next)

theorem packedTransitionOverlap
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.packedTransitionOverlapCode
      (Code.packedTransitionInput periodicStrip current next)
      [(current.overlapsBool periodicStrip next).toNat]
      (packedTransitionOverlapCost
        periodicStrip current next) := by
  let phase := decide
    (next.phase = (current.phase + 1) % periodicStrip.period)
  let columns := (List.finRange 4).all fun column =>
    current.overlapsColumnBool periodicStrip next column
  have result := boolAnd_fit_bool phase columns
    (by simpa [phase] using
      (packedTransitionPhase periodicStrip current next))
    (by simpa [columns] using
      (packedTransitionOverlapColumns periodicStrip current next))
  change EvaluatorCodeFits Code.packedTransitionOverlapCode
    (Code.packedTransitionInput periodicStrip current next)
    [(phase && columns).toNat] _
  simpa [Code.packedTransitionOverlapCode,
    packedTransitionOverlapCost, phase, columns] using result

def packedTransitionTailCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let center := current.isCenterValidBool tromino periodicStrip
  let overlap := current.overlapsBool periodicStrip next
  boolAndCost values center.toNat overlap.toNat
    (packedTransitionCenterCost tromino periodicStrip current next)
    (packedTransitionOverlapCost periodicStrip current next)

theorem packedTransitionTail
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      (Code.boolAnd (Code.packedTransitionCenterCode tromino)
        Code.packedTransitionOverlapCode)
      (Code.packedTransitionInput periodicStrip current next)
      [((current.isCenterValidBool tromino periodicStrip) &&
        current.overlapsBool periodicStrip next).toNat]
      (packedTransitionTailCost
        tromino periodicStrip current next) := by
  exact boolAnd_fit_bool
    (current.isCenterValidBool tromino periodicStrip)
    (current.overlapsBool periodicStrip next)
    (packedTransitionCenter
      tromino periodicStrip wellFormed current next)
    (packedTransitionOverlap periodicStrip current next)

def packedTransitionCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.packedTransitionInput periodicStrip current next
  let normalized := current.isNormalizedBool periodicStrip
  let tail := current.isCenterValidBool tromino periodicStrip &&
    current.overlapsBool periodicStrip next
  boolAndCost values normalized.toNat tail.toNat
    (packedTransitionNormalizationCost periodicStrip current next)
    (packedTransitionTailCost tromino periodicStrip current next)

/-- Exact fitted certificate for the complete packed transition evaluator. -/
theorem packedTransition
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.packedTransitionCode tromino)
      (Code.packedTransitionInput periodicStrip current next)
      [(current.transitionBool tromino periodicStrip next).toNat]
      (packedTransitionCost tromino periodicStrip current next) := by
  let normalized := current.isNormalizedBool periodicStrip
  let center := current.isCenterValidBool tromino periodicStrip
  let overlap := current.overlapsBool periodicStrip next
  have result := boolAnd_fit_bool normalized (center && overlap)
    (by simpa [normalized] using
      (packedTransitionNormalization periodicStrip current next))
    (by simpa [center, overlap] using
      (packedTransitionTail
        tromino periodicStrip wellFormed current next))
  change EvaluatorCodeFits (Code.packedTransitionCode tromino)
    (Code.packedTransitionInput periodicStrip current next)
    [(normalized && center && overlap).toNat] _
  simpa [Code.packedTransitionCode, packedTransitionCost,
    normalized, center, overlap, Bool.and_assoc] using result

end EvaluatorCodeFits

end PartrecToTM2
end Turing
