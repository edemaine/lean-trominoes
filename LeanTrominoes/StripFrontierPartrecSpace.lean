import LeanTrominoes.StripFrontierCyclePartrec
import LeanTrominoes.StripFrontierIndexedSearchSpace
import LeanTrominoes.PartrecEvaluatorSpaceRefinement
import LeanTrominoes.PartrecBinaryLengthSpace
import LeanTrominoes.PartrecFuelSpace
import LeanTrominoes.PartrecPowerTwoSpace
import LeanTrominoes.PartrecStripWellFormedSpace
import LeanTrominoes.PartrecStripTransitionSpace

/-!
# Space bounds for compiled strip-search payloads

The Savitch evaluator may take exponential time, so its exact countdown fuel
is itself exponentially large as a natural number.  Its binary representation
is nevertheless quadratic in the strip input length.  This module proves that
fact and combines it with the flat DFS-state bound to control every semantic
reachability-loop payload.
-/

namespace LeanTrominoes
namespace FiniteState

open Computability

theorem divideEvalFuel_pos (stateCount depth : Nat) :
    0 < divideEvalFuel stateCount depth := by
  induction depth with
  | zero => simp [divideEvalFuel]
  | succ depth induction =>
      simp only [divideEvalFuel]
      omega

/-- An exponential numeric bound whose exponent is only the product of the
recursion depth and the bit width of the graph-state count. -/
theorem divideEvalFuel_le_pow
    (stateCount depth bits : Nat)
    (stateCountBound : stateCount ≤ 2 ^ bits) :
    divideEvalFuel stateCount depth ≤
      2 ^ ((depth + 1) * (bits + 3)) := by
  induction depth with
  | zero =>
      simp only [divideEvalFuel]
      exact one_le_pow₀ (by omega)
  | succ depth induction =>
      let fuel := divideEvalFuel stateCount depth
      let previousPower := 2 ^ ((depth + 1) * (bits + 3))
      have fuelBound : fuel ≤ previousPower := induction
      have previousPositive : 0 < previousPower := by
        exact pow_pos (by omega) _
      have innerBound : 2 * fuel + 2 ≤ 4 * previousPower := by
        omega
      have productBound :
          stateCount * (2 * fuel + 2) ≤
            2 ^ bits * (4 * previousPower) :=
        Nat.mul_le_mul stateCountBound innerBound
      have factorPositive : 0 < 2 ^ (bits + 2) * previousPower := by
        positivity
      have exponentIdentity :
          (depth + 2) * (bits + 3) =
            (bits + 3) + (depth + 1) * (bits + 3) := by
        ring
      simp only [divideEvalFuel]
      change 1 + stateCount * (2 * fuel + 2) ≤ _
      rw [exponentIdentity, pow_add]
      have factorIdentity :
          2 ^ bits * (4 * previousPower) =
            2 ^ (bits + 2) * previousPower := by
        rw [show bits + 2 = bits + 2 from rfl, pow_add]
        ring
      rw [factorIdentity] at productBound
      have powerIdentity :
          2 ^ (bits + 3) * previousPower =
            2 * (2 ^ (bits + 2) * previousPower) := by
        rw [show bits + 3 = 1 + (bits + 2) by omega, pow_add]
        ring
      rw [powerIdentity]
      omega

theorem divideEvalFuel_lt_pow_succ
    (stateCount depth bits : Nat)
    (stateCountBound : stateCount ≤ 2 ^ bits) :
    divideEvalFuel stateCount depth <
      2 ^ (((depth + 1) * (bits + 3)) + 1) := by
  exact (divideEvalFuel_le_pow stateCount depth bits stateCountBound).trans_lt
    (Nat.pow_lt_pow_right (by omega) (by omega))

end FiniteState

namespace PeriodicStrip
namespace RawWindowState

open Computability
open Turing.PartrecToTM2

/-- Binary cells sufficient for the exact reachability countdown fuel. -/
def stripFuelBits (inputLength : Nat) : Nat :=
  (21 * inputLength + 2) * (21 * inputLength + 5) + 1

/-- Space for a countdown plus its context, counters, and flat DFS state. -/
def stripReachPayloadSpaceBound (inputLength : Nat) : Nat :=
  stripDFSPartrecSpaceBound inputLength +
    stripFuelBits inputLength + 43 * inputLength + 8

noncomputable def stripReachPayloadSpacePolynomial : Polynomial Nat :=
  stripDFSPartrecSpacePolynomial +
    ((21 * Polynomial.X + 2) * (21 * Polynomial.X + 5) + 1) +
    43 * Polynomial.X + 8

@[simp]
theorem stripReachPayloadSpacePolynomial_eval (inputLength : Nat) :
    stripReachPayloadSpacePolynomial.eval inputLength =
      stripReachPayloadSpaceBound inputLength := by
  simp [stripReachPayloadSpacePolynomial, stripReachPayloadSpaceBound,
    stripFuelBits]

theorem stripFuel_encodeNat_length_le (periodicStrip : PeriodicStrip) :
    (Computability.encodeNat
      (FiniteState.divideEvalFuel
        (indexCount periodicStrip)
        (stripSearchDepth periodicStrip))).length ≤
      stripFuelBits
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let depth := stripSearchDepth periodicStrip
  let bits := depth + 1
  have fuelBound :=
    FiniteState.divideEvalFuel_lt_pow_succ
      (indexCount periodicStrip) depth bits
      (indexCount_le_pow_stripSearchDepth_succ periodicStrip)
  have encodedBound :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ fuelBound
  simpa [inputLength, depth, bits, stripSearchDepth, stripFuelBits] using
    encodedBound

/-- Every semantic milestone of one exact-fuel reachability loop, including
the leading countdown and immutable strip context, has quadratic native-list
space. -/
theorem stripReachPayload_encodedListSpace_le
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (first last steps : Nat)
    (firstBelow : first < indexCount periodicStrip)
    (lastBelow : last < indexCount periodicStrip) :
    encodedListSpace
        (FiniteState.divideEvalFuel
            (indexCount periodicStrip)
            (stripSearchDepth periodicStrip) ::
          FiniteState.divideEvalProgramList
            (Encodable.encode periodicStrip)
            (indexCount periodicStrip)
            ((FiniteState.divideEvalStep
              (indexCount periodicStrip)
              (indexedTransitionRawBool tromino periodicStrip))^[steps]
                (FiniteState.divideEvalInitial
                  (stripSearchDepth periodicStrip) first last))) ≤
      stripReachPayloadSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let depth := stripSearchDepth periodicStrip
  let bits := depth + 1
  let state :=
    ((FiniteState.divideEvalStep
      (indexCount periodicStrip)
      (indexedTransitionRawBool tromino periodicStrip))^[steps]
        (FiniteState.divideEvalInitial depth first last))
  have fuelBits := stripFuel_encodeNat_length_le periodicStrip
  have stateSpace :=
    stripDivideEvalIterate_encodedListSpace_le periodicStrip
      (indexedTransitionRawBool tromino periodicStrip)
      first last steps firstBelow lastBelow
  have countPow :
      indexCount periodicStrip < 2 ^ (bits + 1) :=
    (indexCount_le_pow_stripSearchDepth_succ periodicStrip).trans_lt
      (Nat.pow_lt_pow_right (by omega) (by omega))
  have countBits :
      (Computability.encodeNat (indexCount periodicStrip)).length ≤ bits + 1 :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ countPow
  have stackLength :
      state.stack.length ≤ depth :=
    FiniteState.divideEvalIterate_stack_length_le_depth
      (indexCount periodicStrip) depth first last steps
      (indexedTransitionRawBool tromino periodicStrip)
  have stackPow : state.stack.length < 2 ^ bits :=
    stackLength.trans_lt
      (stripSearchDepth_lt_pow_succ periodicStrip)
  have stackBits :
      (Computability.encodeNat state.stack.length).length ≤ bits :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ stackPow
  have contextSpace :
      (Computability.encodeNat (Encodable.encode periodicStrip)).length + 1 =
        inputLength := by
    simp [inputLength]
  have fuelBits' :
      (Computability.encodeNat
        (FiniteState.divideEvalFuel
          (indexCount periodicStrip) depth)).length ≤
        stripFuelBits inputLength := by
    simpa [depth, inputLength] using fuelBits
  have stateSpace' :
      encodedListSpace state.toNatList ≤
        stripDFSPartrecSpaceBound inputLength := by
    simpa [state, depth, inputLength] using stateSpace
  have bitsEq : bits = 21 * inputLength + 2 := by
    simp [bits, depth, inputLength, stripSearchDepth]
  change
    encodedListSpace
      (FiniteState.divideEvalFuel (indexCount periodicStrip) depth ::
        Encodable.encode periodicStrip ::
          indexCount periodicStrip :: state.stack.length ::
            state.toNatList) ≤ _
  simp only [encodedListSpace_cons]
  rw [contextSpace]
  change _ ≤ stripReachPayloadSpaceBound inputLength
  simp only [stripReachPayloadSpaceBound]
  omega

/-- A uniform linear bound for the serialized counters surrounding one
reachability call.  The larger seven-field inner-loop shape also bounds the
six-field outer-loop shape. -/
def stripLoopPayloadSpaceBound (inputLength : Nat) : Nat :=
  106 * inputLength + 21

noncomputable def stripLoopPayloadSpacePolynomial : Polynomial Nat :=
  106 * Polynomial.X + 21

@[simp]
theorem stripLoopPayloadSpacePolynomial_eval (inputLength : Nat) :
    stripLoopPayloadSpacePolynomial.eval inputLength =
      stripLoopPayloadSpaceBound inputLength := by
  simp [stripLoopPayloadSpacePolynomial, stripLoopPayloadSpaceBound]

/-- Any endpoint countdown bounded by the frontier-state count has linear
binary length.  This includes the count itself. -/
theorem stripCounter_encodeNat_length_le
    (periodicStrip : PeriodicStrip) (counter : Nat)
    (counterBound : counter ≤ indexCount periodicStrip) :
    (Computability.encodeNat counter).length ≤
      21 *
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length + 3 := by
  let depth := stripSearchDepth periodicStrip
  have countPow :
      indexCount periodicStrip <
        2 ^ ((depth + 1) + 1) :=
    (indexCount_le_pow_stripSearchDepth_succ periodicStrip).trans_lt
      (Nat.pow_lt_pow_right (by omega) (by omega))
  have counterPow : counter < 2 ^ ((depth + 1) + 1) :=
    counterBound.trans_lt countPow
  have encodedBound :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ counterPow
  simpa [depth, stripSearchDepth] using encodedBound

/-- For bounded frontier indices, the common transition-context envelope is
linear in the original encoded strip input length. -/
theorem stripFrontierContextPolynomialSpaceUnit_le_inputLength
    (periodicStrip : PeriodicStrip) (first last : Nat)
    (firstBound : first < indexCount periodicStrip)
    (lastBound : last < indexCount periodicStrip) :
    Turing.PartrecToTM2.EvaluatorCodeFits.stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last ≤
      100 *
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length + 100 := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let stripCode := Encodable.encode periodicStrip
  let limit :=
    Turing.PartrecToTM2.EvaluatorCodeFits.stripFrontierContextPolynomialSpaceLimit
        periodicStrip first last
  have stripBits :
      (Computability.encodeNat stripCode).length + 1 = inputLength := by
    simp [stripCode, inputLength]
  have firstBits := stripCounter_encodeNat_length_le periodicStrip first
    (Nat.le_of_lt firstBound)
  have lastBits := stripCounter_encodeNat_length_le periodicStrip last
    (Nat.le_of_lt lastBound)
  have sum1 :=
    Turing.PartrecToTM2.encodeNat_add_length_le_sum
      stripCode first
  have sum2 :=
    Turing.PartrecToTM2.encodeNat_add_length_le_sum
      (stripCode + first) last
  have sum3 :=
    Turing.PartrecToTM2.encodeNat_add_length_le_sum
      (stripCode + first + last) 100
  have scaled :=
    Turing.PartrecToTM2.encodeNat_mul_length_le_sum
      64 (stripCode + first + last + 100)
  have final :=
    Turing.PartrecToTM2.encodeNat_add_length_le_sum
      (64 * (stripCode + first + last + 100)) 1000
  have sixtyFourBits :
      (Computability.encodeNat 64).length = 7 := by native_decide
  have hundredBits :
      (Computability.encodeNat 100).length = 7 := by native_decide
  have thousandBits :
      (Computability.encodeNat 1000).length = 10 := by native_decide
  have limitEq :
      limit = 64 * (stripCode + first + last + 100) + 1000 := by
    simp [limit,
      Turing.PartrecToTM2.EvaluatorCodeFits.stripFrontierContextPolynomialSpaceLimit,
      stripCode]
  rw [← limitEq] at final
  rw [sixtyFourBits] at scaled
  rw [hundredBits] at sum3
  rw [thousandBits] at final
  have contextEq :
      Turing.PartrecToTM2.EvaluatorCodeFits.stripFrontierContextPolynomialSpaceUnit
            periodicStrip first last =
        (Computability.encodeNat limit).length + 2 := by
    simp [limit,
      Turing.PartrecToTM2.EvaluatorCodeFits.stripFrontierContextPolynomialSpaceUnit,
      Turing.PartrecToTM2.encodedListSpace_cons,
      Turing.PartrecToTM2.encodedListSpace_nil]
  rw [contextEq]
  change (Computability.encodeNat limit).length + 2 ≤
    100 * inputLength + 100
  simp only [inputLength] at firstBits lastBits ⊢
  omega

theorem stripDepth_encodeNat_length_le
    (periodicStrip : PeriodicStrip) :
    (Computability.encodeNat
      (stripSearchDepth periodicStrip)).length ≤
        21 *
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length + 2 := by
  have encodedBound :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _
      (stripSearchDepth_lt_pow_succ periodicStrip)
  simpa [stripSearchDepth] using encodedBound

private theorem divideBoolTag_flatSpace_le (found : Bool) :
    (Computability.encodeNat
      (FiniteState.divideBoolTag found)).length + 1 ≤ 2 := by
  cases found <;> decide

/-- Every semantic payload of the inner endpoint countdown is linear apart
from the nested reachability invocation, which is bounded separately above. -/
theorem stripCandidatePayload_encodedListSpace_le
    (periodicStrip : PeriodicStrip)
    (remaining first secondRemaining : Nat) (found : Bool)
    (remainingBound : remaining ≤ indexCount periodicStrip)
    (firstBound : first ≤ indexCount periodicStrip)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) :
    encodedListSpace
        (remaining ::
          [Encodable.encode periodicStrip, indexCount periodicStrip,
            stripSearchDepth periodicStrip, first, secondRemaining,
            FiniteState.divideBoolTag found]) ≤
      stripLoopPayloadSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  have remainingBits :=
    stripCounter_encodeNat_length_le periodicStrip remaining remainingBound
  have countBits :=
    stripCounter_encodeNat_length_le periodicStrip
      (indexCount periodicStrip) (Nat.le_refl _)
  have firstBits :=
    stripCounter_encodeNat_length_le periodicStrip first firstBound
  have secondBits :=
    stripCounter_encodeNat_length_le periodicStrip
      secondRemaining secondBound
  have depthBits := stripDepth_encodeNat_length_le periodicStrip
  have foundSpace := divideBoolTag_flatSpace_le found
  have contextSpace :
      (Computability.encodeNat (Encodable.encode periodicStrip)).length + 1 =
        inputLength := by
    simp [inputLength]
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  rw [contextSpace]
  change _ ≤ stripLoopPayloadSpaceBound inputLength
  simp only [stripLoopPayloadSpaceBound]
  simp only [inputLength] at remainingBits countBits firstBits secondBits depthBits ⊢
  omega

/-- The outer endpoint countdown is a field shorter than the inner payload
and therefore obeys the same uniform linear bound. -/
theorem stripOuterPayload_encodedListSpace_le
    (periodicStrip : PeriodicStrip)
    (remaining firstRemaining : Nat) (found : Bool)
    (remainingBound : remaining ≤ indexCount periodicStrip)
    (firstBound : firstRemaining ≤ indexCount periodicStrip) :
    encodedListSpace
        (remaining ::
          [Encodable.encode periodicStrip, indexCount periodicStrip,
            stripSearchDepth periodicStrip, firstRemaining,
            FiniteState.divideBoolTag found]) ≤
      stripLoopPayloadSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  have remainingBits :=
    stripCounter_encodeNat_length_le periodicStrip remaining remainingBound
  have countBits :=
    stripCounter_encodeNat_length_le periodicStrip
      (indexCount periodicStrip) (Nat.le_refl _)
  have firstBits :=
    stripCounter_encodeNat_length_le periodicStrip
      firstRemaining firstBound
  have depthBits := stripDepth_encodeNat_length_le periodicStrip
  have foundSpace := divideBoolTag_flatSpace_le found
  have contextSpace :
      (Computability.encodeNat (Encodable.encode periodicStrip)).length + 1 =
        inputLength := by
    simp [inputLength]
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  rw [contextSpace]
  change _ ≤ stripLoopPayloadSpaceBound inputLength
  simp only [stripLoopPayloadSpaceBound]
  simp only [inputLength] at remainingBits countBits firstBits depthBits ⊢
  omega

/-- Core space reserved for the two kinds of semantic search payload,
together with the typed input and constant-size Boolean output. -/
def stripEvaluatorCoreSpaceBound (inputLength : Nat) : Nat :=
  stripReachPayloadSpaceBound inputLength +
    stripLoopPayloadSpaceBound inputLength + inputLength + 2

/-- A deliberately loose linear allowance for the explicit binary-length and
fixed affine arithmetic used to compute the certified search depth. -/
def stripArithmeticSpaceBound (inputLength : Nat) : Nat :=
  1000000000000000 * (inputLength + 1)

/-- A deliberately loose linear allowance for the explicit repeated-doubling
countdown computing the padded power-of-two graph bound. -/
def stripStateBoundComputationSpaceBound (inputLength : Nat) : Nat :=
  1000000000000000000000000000000000000000000000000000000000000 *
    (100 * inputLength + 100)

/-- A deliberately loose quadratic allowance for the explicit nested
countdowns computing the exact Savitch fuel. -/
def stripFuelComputationSpaceBound (inputLength : Nat) : Nat :=
  1000000000000000000000000000000000000000000000000000000000000 *
    (stripFuelBits inputLength + 100 * inputLength + 100)

/-- One tromino-independent coefficient large enough for either explicit
transition leaf used by the strip evaluator. -/
def stripTransitionLeafSpaceCoefficient : Nat :=
  max
    (Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionPolynomialSpaceCoefficient
      Tromino.I)
    (Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionPolynomialSpaceCoefficient
      Tromino.L)

/-- Space reserve for one explicit indexed-transition leaf call. -/
def stripTransitionLeafSpaceBound (inputLength : Nat) : Nat :=
  stripTransitionLeafSpaceCoefficient * (100 * inputLength + 100)

noncomputable def stripTransitionLeafSpacePolynomial : Polynomial Nat :=
  Polynomial.C stripTransitionLeafSpaceCoefficient *
    (100 * Polynomial.X + 100)

set_option maxRecDepth 100000 in
@[simp]
theorem stripTransitionLeafSpacePolynomial_eval (inputLength : Nat) :
    stripTransitionLeafSpacePolynomial.eval inputLength =
      stripTransitionLeafSpaceBound inputLength := by
  unfold stripTransitionLeafSpacePolynomial
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show Polynomial.eval inputLength (100 * Polynomial.X + 100) =
      100 * inputLength + 100 by simp]
  unfold stripTransitionLeafSpaceBound
  rfl

/-- One common polynomial envelope for search payloads and explicit
search-depth and fuel arithmetic. -/
def stripEvaluatorSpaceBound (inputLength : Nat) : Nat :=
  stripEvaluatorCoreSpaceBound inputLength +
    stripArithmeticSpaceBound inputLength +
      stripStateBoundComputationSpaceBound inputLength +
        stripFuelComputationSpaceBound inputLength +
          stripTransitionLeafSpaceBound inputLength

/-- Polynomial packaging of `stripEvaluatorSpaceBound`. -/
noncomputable def stripEvaluatorSpacePolynomial : Polynomial Nat :=
  stripReachPayloadSpacePolynomial +
    stripLoopPayloadSpacePolynomial + Polynomial.X + 2 +
      1000000000000000 * (Polynomial.X + 1) +
        1000000000000000000000000000000000000000000000000000000000000 *
          (100 * Polynomial.X + 100) +
          1000000000000000000000000000000000000000000000000000000000000 *
            (((21 * Polynomial.X + 2) *
              (21 * Polynomial.X + 5) + 1) +
              100 * Polynomial.X + 100) +
            stripTransitionLeafSpacePolynomial

@[simp]
theorem stripEvaluatorSpacePolynomial_eval (inputLength : Nat) :
    stripEvaluatorSpacePolynomial.eval inputLength =
      stripEvaluatorSpaceBound inputLength := by
  simp [stripEvaluatorSpacePolynomial, stripEvaluatorSpaceBound,
    stripEvaluatorCoreSpaceBound, stripArithmeticSpaceBound,
    stripStateBoundComputationSpaceBound,
    stripFuelComputationSpaceBound, stripTransitionLeafSpaceBound,
    stripFuelBits]

theorem stripReachPayloadSpaceBound_le_evaluator
    (inputLength : Nat) :
    stripReachPayloadSpaceBound inputLength ≤
      stripEvaluatorSpaceBound inputLength := by
  simp only [stripEvaluatorSpaceBound,
    stripEvaluatorCoreSpaceBound]
  omega

theorem stripLoopPayloadSpaceBound_le_evaluator
    (inputLength : Nat) :
    stripLoopPayloadSpaceBound inputLength ≤
      stripEvaluatorSpaceBound inputLength := by
  simp only [stripEvaluatorSpaceBound,
    stripEvaluatorCoreSpaceBound]
  omega

theorem stripInputLength_le_evaluator (inputLength : Nat) :
    inputLength ≤ stripEvaluatorSpaceBound inputLength := by
  simp only [stripEvaluatorSpaceBound,
    stripEvaluatorCoreSpaceBound]
  omega

/-- The native evaluator representation of a typed strip input has exactly
the project's binary input length. -/
theorem stripInput_encodedListSpace
    (periodicStrip : PeriodicStrip) :
    encodedListSpace [Encodable.encode periodicStrip] =
      ((Complexity.primcodableFinEncoding PeriodicStrip).encode
        periodicStrip).length := by
  simpa only [Turing.PartrecToTM2.stackSpace_init] using
    Turing.PartrecToTM2.stackSpace_typed_init
      (periodicStripTrominoTilingCode Tromino.I) periodicStrip

private theorem stripEncodingPairBits
    (periodicStrip : PeriodicStrip) :
    (Computability.encodeNat
      (Nat.pair periodicStrip.width
        (Nat.pair periodicStrip.period
          (Encodable.encode periodicStrip.motif)))).length =
      (Computability.encodeNat
        (Encodable.encode periodicStrip)).length := by
  rw [PeriodicStrip.encode_eq_pair]

/-- The explicit repeated-doubling program fits the linear reserve assigned
to the padded power-of-two state bound. -/
theorem stripStateBoundCodeCost_le
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits.powerTwoCost
        (stripSearchDepth periodicStrip) ≤
      stripStateBoundComputationSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let depth := stripSearchDepth periodicStrip
  have depthValue : depth = 21 * inputLength + 1 := by
    simp [depth, inputLength, stripSearchDepth]
  have depthBits :
      (Computability.encodeNat depth).length ≤
        21 * inputLength + 2 := by
    simpa [depth, inputLength] using
      stripDepth_encodeNat_length_le periodicStrip
  have depthSuccessorBits :=
    encodeNat_succ_length_le depth
  have depthPlusBits :
      (Computability.encodeNat (depth + 1)).length ≤
        (Computability.encodeNat depth).length + 1 := by
    simpa [Nat.succ_eq_add_one] using depthSuccessorBits
  have stateBoundPow :
      2 ^ depth < 2 ^ (depth + 1) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have stateBoundBits :
      (Computability.encodeNat (2 ^ depth)).length ≤ depth + 1 :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ stateBoundPow
  have inputLengthDirect :
      (Computability.encodeNat
          (Encodable.encode periodicStrip)).length + 1 =
        inputLength := by
    simp [inputLength]
  have depthDirectBits :
      (Computability.encodeNat
        (stripSearchDepth periodicStrip)).length =
        (Computability.encodeNat depth).length := by
    rfl
  have depthPlusDirectBits :
      (Computability.encodeNat
        (stripSearchDepth periodicStrip + 1)).length =
        (Computability.encodeNat (depth + 1)).length := by
    rfl
  have stateBoundDirectBits :
      (Computability.encodeNat
        (2 ^ stripSearchDepth periodicStrip)).length =
        (Computability.encodeNat (2 ^ depth)).length := by
    rfl
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have pairBits := stripEncodingPairBits periodicStrip
  simp [EvaluatorCodeFits.powerTwoCost,
    EvaluatorCodeFits.powerTwoInputCost,
    EvaluatorCodeFits.powerTwoLoopCost,
    stripStateBoundComputationSpaceBound,
    EvaluatorCodeFits.prependCost,
    EvaluatorCodeFits.idCost,
    EvaluatorCodeFits.headCost,
    EvaluatorCodeFits.nilCost,
    EvaluatorCodeFits.oneCost,
    EvaluatorCodeFits.zeroCost,
    EvaluatorCodeFits.zeroPrimeCost,
    EvaluatorCodeFits.tailCost,
    EvaluatorCodeFits.succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits, oneBits]
  omega

/-- The complete explicit fuel computation fits its quadratic arithmetic
reserve. -/
theorem stripFuelCodeCost_le
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits.divideEvalFuelCost
        [indexCount periodicStrip,
          stripSearchDepth periodicStrip] ≤
      stripFuelComputationSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let stateCount := indexCount periodicStrip
  let depth := stripSearchDepth periodicStrip
  let fuel :=
    FiniteState.divideEvalFuel stateCount depth
  have countBits :
      (Computability.encodeNat stateCount).length ≤
        21 * inputLength + 3 := by
    simpa [stateCount, inputLength] using
      stripCounter_encodeNat_length_le periodicStrip
        stateCount (Nat.le_refl _)
  have depthBits :
      (Computability.encodeNat depth).length ≤
        21 * inputLength + 2 := by
    simpa [depth, inputLength] using
      stripDepth_encodeNat_length_le periodicStrip
  have fuelBits :
      (Computability.encodeNat fuel).length ≤
        stripFuelBits inputLength := by
    simpa [fuel, stateCount, depth, inputLength] using
      stripFuel_encodeNat_length_le periodicStrip
  have countSuccessorBits :=
    encodeNat_succ_length_le stateCount
  have countPlusBits :
      (Computability.encodeNat (stateCount + 1)).length ≤
        (Computability.encodeNat stateCount).length + 1 := by
    simpa [Nat.succ_eq_add_one] using countSuccessorBits
  have depthSuccessorBits :=
    encodeNat_succ_length_le depth
  have depthPlusBits :
      (Computability.encodeNat (depth + 1)).length ≤
        (Computability.encodeNat depth).length + 1 := by
    simpa [Nat.succ_eq_add_one] using depthSuccessorBits
  have fuelSuccessorBits :=
    encodeNat_succ_length_le fuel
  have fuelPlusBits :
      (Computability.encodeNat (fuel + 1)).length ≤
        (Computability.encodeNat fuel).length + 1 := by
    simpa [Nat.succ_eq_add_one] using fuelSuccessorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have pairBits := stripEncodingPairBits periodicStrip
  have pairFuelBits :
      stripFuelBits
          ((Computability.encodeNat
            (Nat.pair periodicStrip.width
              (Nat.pair periodicStrip.period
                (Encodable.encode periodicStrip.motif)))).length + 1) =
        stripFuelBits
          ((Computability.encodeNat
            (Encodable.encode periodicStrip)).length + 1) := by
    rw [pairBits]
  have inputLengthDirect :
      (Computability.encodeNat
          (Encodable.encode periodicStrip)).length + 1 =
        inputLength := by
    simp [inputLength]
  have fuelBoundDirect :
      stripFuelBits
          ((Computability.encodeNat
            (Encodable.encode periodicStrip)).length + 1) =
        stripFuelBits inputLength := by
    rw [inputLengthDirect]
  have countDirectBits :
      (Computability.encodeNat
        (indexCount periodicStrip)).length =
        (Computability.encodeNat stateCount).length := by
    rfl
  have depthDirectBits :
      (Computability.encodeNat
        (stripSearchDepth periodicStrip)).length =
        (Computability.encodeNat depth).length := by
    rfl
  have fuelDirectBits :
      (Computability.encodeNat
        (FiniteState.divideEvalFuel
          (indexCount periodicStrip)
          (stripSearchDepth periodicStrip))).length =
        (Computability.encodeNat fuel).length := by
    rfl
  have countPlusDirectBits :
      (Computability.encodeNat
        (indexCount periodicStrip + 1)).length =
        (Computability.encodeNat (stateCount + 1)).length := by
    rfl
  have depthPlusDirectBits :
      (Computability.encodeNat
        (stripSearchDepth periodicStrip + 1)).length =
        (Computability.encodeNat (depth + 1)).length := by
    rfl
  have fuelPlusDirectBits :
      (Computability.encodeNat
        (FiniteState.divideEvalFuel
          (indexCount periodicStrip)
          (stripSearchDepth periodicStrip) + 1)).length =
        (Computability.encodeNat (fuel + 1)).length := by
    rfl
  simp [EvaluatorCodeFits.divideEvalFuelCost,
    EvaluatorCodeFits.divideEvalFuelInputCost,
    EvaluatorCodeFits.fuelOuterLoopCost,
    stripFuelComputationSpaceBound,
    EvaluatorCodeFits.prependCost,
    EvaluatorCodeFits.getCost,
    EvaluatorCodeFits.dropCost,
    EvaluatorCodeFits.idCost,
    EvaluatorCodeFits.headCost,
    EvaluatorCodeFits.nilCost,
    EvaluatorCodeFits.oneCost,
    EvaluatorCodeFits.zeroCost,
    EvaluatorCodeFits.zeroPrimeCost,
    EvaluatorCodeFits.tailCost,
    EvaluatorCodeFits.succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits, oneBits]
  omega

/-- The explicit search-depth program fits the arithmetic part of the strip
budget whenever the surrounding continuation fits the reserved core. -/
theorem stripSearchDepthCode_fits
    (periodicStrip : PeriodicStrip)
    (continuation : Turing.ToPartrec.Cont)
    (continuationBound :
      continuationSpace continuation ≤
        stripEvaluatorCoreSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length)
    (after :
      EvaluatorExecutionFits
        (stripEvaluatorSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length)
        (.ret continuation [stripSearchDepth periodicStrip])) :
    EvaluatorCallFits stripSearchDepthCode continuation
      [Encodable.encode periodicStrip]
      (stripEvaluatorSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length) := by
  let number := Encodable.encode periodicStrip
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  change
    continuationSpace continuation ≤
      stripEvaluatorCoreSpaceBound inputLength at continuationBound
  have fits :=
    EvaluatorCodeFits.binaryLengthAffine21Code number
  have inputSpace :
      encodedListSpace [number] = inputLength := by
    dsimp [number, inputLength]
    exact stripInput_encodedListSpace periodicStrip
  have resultEq :
      22 + 21 *
          LeanTrominoes.Computability.binaryEncodingLength number =
        stripSearchDepth periodicStrip := by
    simp [number, stripSearchDepth,
      LeanTrominoes.Computability.binaryEncodingLength_eq,
      Complexity.primcodableFinEncoding_encode_length]
    ring
  have after' :
      EvaluatorExecutionFits
        (stripEvaluatorSpaceBound inputLength)
        (.ret continuation
          [22 + 21 *
            LeanTrominoes.Computability.binaryEncodingLength number]) := by
    rw [resultEq]
    exact after
  change
    EvaluatorCallFits
      (Turing.ToPartrec.Code.binaryLengthAffineCode 21 22)
      continuation [number]
      (stripEvaluatorSpaceBound inputLength)
  exact
    fits.call continuation
      (stripEvaluatorSpaceBound inputLength)
      (by
        simp only [EvaluatorCodeFits.binaryLengthAffine21Cost,
          inputSpace, stripEvaluatorSpaceBound,
          stripArithmeticSpaceBound]
        omega)
      after'

/-- The complete state-bound program composes the fitted search-depth
calculation with the fitted power-of-two countdown. -/
theorem stripStateBoundCode_fits
    (periodicStrip : PeriodicStrip)
    (continuation : Turing.ToPartrec.Cont)
    (continuationBound :
      continuationSpace continuation ≤
        stripEvaluatorCoreSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length)
    (after :
      EvaluatorExecutionFits
        (stripEvaluatorSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length)
        (.ret continuation [stripStateBound periodicStrip])) :
    EvaluatorCallFits stripStateBoundCode continuation
      [Encodable.encode periodicStrip]
      (stripEvaluatorSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length) := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let depth := stripSearchDepth periodicStrip
  have continuationBound' :
      continuationSpace continuation ≤
        stripEvaluatorCoreSpaceBound inputLength := by
    simpa [inputLength] using continuationBound
  have powerFits := EvaluatorCodeFits.powerTwo depth
  have powerCostBound :
      EvaluatorCodeFits.powerTwoCost depth ≤
        stripStateBoundComputationSpaceBound inputLength := by
    simpa [depth, inputLength] using
      stripStateBoundCodeCost_le periodicStrip
  have afterPower :
      EvaluatorExecutionFits
        (stripEvaluatorSpaceBound inputLength)
        (.ret continuation [2 ^ depth]) := by
    simpa [stripStateBound, depth, inputLength] using after
  have powerCall :
      EvaluatorCallFits Turing.ToPartrec.Code.powerTwoCode
        continuation [depth]
        (stripEvaluatorSpaceBound inputLength) :=
    powerFits.call continuation
      (stripEvaluatorSpaceBound inputLength)
      (by
        simp only [stripEvaluatorSpaceBound]
        omega)
      afterPower
  let powerContinuation :=
    Turing.ToPartrec.Cont.comp
      Turing.ToPartrec.Code.powerTwoCode continuation
  have afterDepth :
      EvaluatorExecutionFits
        (stripEvaluatorSpaceBound inputLength)
        (.ret powerContinuation [depth]) := by
    apply EvaluatorExecutionFits.ret_comp
    · simp only [continuationSpace_comp]
      have depthInputSpace :=
        powerFits.input_space
      simp only [stripEvaluatorSpaceBound]
      omega
    · exact powerCall
  have depthCall :
      EvaluatorCallFits stripSearchDepthCode
        powerContinuation [Encodable.encode periodicStrip]
        (stripEvaluatorSpaceBound inputLength) := by
    apply stripSearchDepthCode_fits periodicStrip
    · simpa [powerContinuation, inputLength] using continuationBound'
    · simpa [depth, inputLength] using afterDepth
  have whole := EvaluatorCallFits.comp depthCall
  simpa [stripStateBoundCode, powerContinuation, inputLength] using whole

/-- The explicit exact-fuel program fits the fuel-computation part of the
strip budget whenever the surrounding continuation fits the preceding
reserves. -/
theorem stripFuelCode_fits
    (periodicStrip : PeriodicStrip)
    (continuation : Turing.ToPartrec.Cont)
    (continuationBound :
      continuationSpace continuation ≤
        stripEvaluatorCoreSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length +
        stripArithmeticSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length +
        stripStateBoundComputationSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length)
    (after :
      EvaluatorExecutionFits
        (stripEvaluatorSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length)
        (.ret continuation
          [FiniteState.divideEvalFuel
            (indexCount periodicStrip)
            (stripSearchDepth periodicStrip)])) :
    EvaluatorCallFits divideEvalFuelCode continuation
      [indexCount periodicStrip, stripSearchDepth periodicStrip]
      (stripEvaluatorSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length) := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let values :=
    [indexCount periodicStrip, stripSearchDepth periodicStrip]
  have fits := EvaluatorCodeFits.divideEvalFuel values
  have costBound :
      EvaluatorCodeFits.divideEvalFuelCost values ≤
        stripFuelComputationSpaceBound inputLength := by
    simpa [values, inputLength] using
      stripFuelCodeCost_le periodicStrip
  have call :=
    fits.call continuation
      (stripEvaluatorSpaceBound inputLength)
      (by
        simp only [stripEvaluatorSpaceBound]
        change continuationSpace continuation ≤
          stripEvaluatorCoreSpaceBound inputLength +
            stripArithmeticSpaceBound inputLength +
              stripStateBoundComputationSpaceBound inputLength
          at continuationBound
        omega)
      (by
        change
          EvaluatorExecutionFits
            (stripEvaluatorSpaceBound inputLength)
            (.ret continuation
              [FiniteState.divideEvalFuel
                (values[0]?.getD 0) (values[1]?.getD 0)]) at after
        exact after)
  simpa [divideEvalFuelCode, values, inputLength] using call

/-- A Boolean result occupies at most two cells in the evaluator's
delimited-binary list representation. -/
theorem stripResult_encodedListSpace_le (result : Bool) :
    encodedListSpace [Encodable.encode result] ≤ 2 := by
  cases result <;> decide

/-- The explicit well-formedness program consumes only the arithmetic
allowance; all other strip-evaluator reserves remain available to its
continuation. -/
theorem stripWellFormedCode_fits
    (periodicStrip : PeriodicStrip)
    (continuation : Turing.ToPartrec.Cont)
    (continuationBound :
      continuationSpace continuation ≤
        stripEvaluatorCoreSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length +
        stripStateBoundComputationSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length +
        stripFuelComputationSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length)
    (after :
      EvaluatorExecutionFits
        (stripEvaluatorSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length)
        (.ret continuation
          [FiniteState.divideBoolTag periodicStrip.wellFormed])) :
    EvaluatorCallFits stripWellFormedCode continuation
      [Encodable.encode periodicStrip]
      (stripEvaluatorSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length) := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  have inputSpace :
      encodedListSpace [Encodable.encode periodicStrip] =
        inputLength := by
    dsimp only [inputLength]
    exact stripInput_encodedListSpace periodicStrip
  have fits :=
    Turing.PartrecToTM2.EvaluatorCodeFits.stripWellFormedExplicitInputSpace
      periodicStrip
  have after' :
      EvaluatorExecutionFits
        (stripEvaluatorSpaceBound inputLength)
        (.ret continuation [periodicStrip.wellFormed.toNat]) := by
    cases wellFormed : periodicStrip.wellFormed <;>
      simpa [inputLength, wellFormed,
        FiniteState.divideBoolTag] using after
  have call :=
    fits.call continuation
      (stripEvaluatorSpaceBound inputLength)
      (by
        simp only [
          Turing.PartrecToTM2.EvaluatorCodeFits.stripWellFormedInputSpaceBound,
          inputSpace, stripEvaluatorSpaceBound,
          stripArithmeticSpaceBound]
        change continuationSpace continuation ≤
          stripEvaluatorCoreSpaceBound inputLength +
            stripStateBoundComputationSpaceBound inputLength +
              stripFuelComputationSpaceBound inputLength
          at continuationBound
        omega)
      after'
  simpa [stripWellFormedCode, inputLength] using call

/-- Either tromino's base-leaf coefficient is covered by the common evaluator
reserve. -/
theorem stripBaseTransitionPolynomialSpaceCoefficient_le_leaf
    (tromino : Tromino) :
    Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionPolynomialSpaceCoefficient
        tromino ≤
      stripTransitionLeafSpaceCoefficient := by
  cases tromino <;> simp [stripTransitionLeafSpaceCoefficient]

/-- The edge coefficient is no larger than the base leaf that contains it. -/
theorem stripTransitionPolynomialSpaceCoefficient_le_base
    (tromino : Tromino) :
    Turing.PartrecToTM2.EvaluatorCodeFits.stripTransitionPolynomialSpaceCoefficient
        tromino ≤
      Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionPolynomialSpaceCoefficient
        tromino := by
  simp only [
    Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionPolynomialSpaceCoefficient,
    Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionComponentSpaceCoefficient]
  omega

/-- A bounded depth-zero transition leaf fits the common input-length
reserve. -/
theorem stripBaseTransitionPolynomialSpaceBound_le_leaf
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat)
    (firstBound : first < indexCount periodicStrip)
    (lastBound : last < indexCount periodicStrip) :
    Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionPolynomialSpaceBound
          tromino periodicStrip first last ≤
      stripTransitionLeafSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  have localBound :=
    Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionPolynomialSpaceBound_le_contextUnit
        tromino periodicStrip first last
  have context :=
    stripFrontierContextPolynomialSpaceUnit_le_inputLength
      periodicStrip first last firstBound lastBound
  have coefficient :=
    stripBaseTransitionPolynomialSpaceCoefficient_le_leaf tromino
  calc
    _ ≤
        Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionPolynomialSpaceCoefficient
            tromino *
          Turing.PartrecToTM2.EvaluatorCodeFits.stripFrontierContextPolynomialSpaceUnit
              periodicStrip first last := localBound
    _ ≤
        Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionPolynomialSpaceCoefficient
            tromino *
          (100 * inputLength + 100) := Nat.mul_le_mul_left _ context
    _ ≤ stripTransitionLeafSpaceCoefficient *
          (100 * inputLength + 100) :=
      Nat.mul_le_mul_right _ coefficient
    _ = _ := by simp [stripTransitionLeafSpaceBound, inputLength]

/-- A bounded raw-edge leaf fits the same common input-length reserve. -/
theorem stripTransitionPolynomialSpaceBound_le_leaf
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat)
    (firstBound : first < indexCount periodicStrip)
    (lastBound : last < indexCount periodicStrip) :
    Turing.PartrecToTM2.EvaluatorCodeFits.stripTransitionPolynomialSpaceBound
          tromino periodicStrip first last ≤
      stripTransitionLeafSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  have localBound :=
    Turing.PartrecToTM2.EvaluatorCodeFits.stripTransitionPolynomialSpaceBound_le_contextUnit
        tromino periodicStrip first last
  have context :=
    stripFrontierContextPolynomialSpaceUnit_le_inputLength
      periodicStrip first last firstBound lastBound
  have coefficient :=
    (stripTransitionPolynomialSpaceCoefficient_le_base tromino).trans
      (stripBaseTransitionPolynomialSpaceCoefficient_le_leaf tromino)
  calc
    _ ≤
        Turing.PartrecToTM2.EvaluatorCodeFits.stripTransitionPolynomialSpaceCoefficient
            tromino *
          Turing.PartrecToTM2.EvaluatorCodeFits.stripFrontierContextPolynomialSpaceUnit
              periodicStrip first last := localBound
    _ ≤
        Turing.PartrecToTM2.EvaluatorCodeFits.stripTransitionPolynomialSpaceCoefficient
            tromino *
          (100 * inputLength + 100) := Nat.mul_le_mul_left _ context
    _ ≤ stripTransitionLeafSpaceCoefficient *
          (100 * inputLength + 100) :=
      Nat.mul_le_mul_right _ coefficient
    _ = _ := by simp [stripTransitionLeafSpaceBound, inputLength]

/-- Fitted-call obligations for the two explicit transition leaves used by
the strip evaluator.  Each field is continuation-passing: the caller reserves
the common leaf allowance alongside its continuation and supplies the fitted
execution after the verified Boolean result is returned. -/
structure StripEvaluatorLeafCallsFit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (bound : Nat) : Prop where
  base :
    ∀ first last continuation,
      first < indexCount periodicStrip →
      last < indexCount periodicStrip →
      stripTransitionLeafSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length +
        continuationSpace continuation ≤ bound →
      EvaluatorExecutionFits bound
        (.ret continuation
          [FiniteState.divideBoolTag
            (decide (first = last) ||
              indexedTransitionRawBool tromino periodicStrip
                first last)]) →
      EvaluatorCallFits (stripBaseVectorCode tromino)
        continuation
        [Encodable.encode periodicStrip, first, last] bound
  edge :
    ∀ first last continuation,
      first < indexCount periodicStrip →
      last < indexCount periodicStrip →
      stripTransitionLeafSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length +
        continuationSpace continuation ≤ bound →
      EvaluatorExecutionFits bound
        (.ret continuation
          [FiniteState.divideBoolTag
            (indexedTransitionRawBool tromino periodicStrip
              first last)]) →
      EvaluatorCallFits (stripEdgeVectorCode tromino)
        continuation
        [Encodable.encode periodicStrip, first, last] bound

/-- The explicit transition programs discharge the complete leaf-call
interface whenever the caller sets aside the common leaf reserve. -/
theorem stripEvaluatorLeafCallsFit_explicit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) (bound : Nat) :
    StripEvaluatorLeafCallsFit tromino periodicStrip bound := by
  constructor
  · intro first last continuation firstBound lastBound reserve after
    have fits :=
      Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransition
        tromino periodicStrip wellFormed first last
    have costPolynomial :=
      Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionCost_le_polynomialSpaceBound
          tromino periodicStrip first last
    have polynomialLeaf :=
      stripBaseTransitionPolynomialSpaceBound_le_leaf
        tromino periodicStrip first last firstBound lastBound
    have costLeaf := costPolynomial.trans polynomialLeaf
    have costReserve :
        Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionCost
            tromino periodicStrip first last +
          continuationSpace continuation ≤ bound := by
      omega
    have after' :
        EvaluatorExecutionFits bound
          (.ret continuation
            [((decide (first = last)) ||
              indexedTransitionRawBool tromino periodicStrip
                first last).toNat]) := by
      cases result :
          ((decide (first = last)) ||
            indexedTransitionRawBool tromino periodicStrip first last) <;>
        simpa [result, FiniteState.divideBoolTag] using after
    have call := fits.call continuation bound costReserve after'
    simpa [stripBaseVectorCode] using call
  · intro first last continuation firstBound lastBound reserve after
    have fits :=
      Turing.PartrecToTM2.EvaluatorCodeFits.stripTransition
        tromino periodicStrip wellFormed first last
    have costPolynomial :=
      Turing.PartrecToTM2.EvaluatorCodeFits.stripTransitionCost_le_polynomialSpaceBound
          tromino periodicStrip first last
    have polynomialLeaf :=
      stripTransitionPolynomialSpaceBound_le_leaf
        tromino periodicStrip first last firstBound lastBound
    have costLeaf := costPolynomial.trans polynomialLeaf
    have costReserve :
        Turing.PartrecToTM2.EvaluatorCodeFits.stripTransitionCost
            tromino periodicStrip first last +
          continuationSpace continuation ≤ bound := by
      omega
    have after' :
        EvaluatorExecutionFits bound
          (.ret continuation
            [(indexedTransitionRawBool tromino periodicStrip
              first last).toNat]) := by
      cases result :
          indexedTransitionRawBool
            tromino periodicStrip first last <;>
        simpa [result, FiniteState.divideBoolTag] using after
    have call := fits.call continuation bound costReserve after'
    simpa [stripEdgeVectorCode] using call

end RawWindowState
end PeriodicStrip
end LeanTrominoes
