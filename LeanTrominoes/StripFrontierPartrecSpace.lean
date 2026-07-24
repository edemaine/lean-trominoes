import LeanTrominoes.StripFrontierCyclePartrec
import LeanTrominoes.StripFrontierIndexedSearchSpace
import LeanTrominoes.PartrecEvaluatorSpaceRefinement
import LeanTrominoes.PartrecBinaryLengthSpace
import LeanTrominoes.PartrecFuelSpace

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

/-- A deliberately loose quadratic allowance for the explicit nested
countdowns computing the exact Savitch fuel. -/
def stripFuelComputationSpaceBound (inputLength : Nat) : Nat :=
  1000000000000000000000000000000000000000000000000000000000000 *
    (stripFuelBits inputLength + 100 * inputLength + 100)

/-- One common polynomial envelope for search payloads and explicit
search-depth and fuel arithmetic. -/
def stripEvaluatorSpaceBound (inputLength : Nat) : Nat :=
  stripEvaluatorCoreSpaceBound inputLength +
    stripArithmeticSpaceBound inputLength +
      stripFuelComputationSpaceBound inputLength

/-- Polynomial packaging of `stripEvaluatorSpaceBound`. -/
noncomputable def stripEvaluatorSpacePolynomial : Polynomial Nat :=
  stripReachPayloadSpacePolynomial +
    stripLoopPayloadSpacePolynomial + Polynomial.X + 2 +
      1000000000000000 * (Polynomial.X + 1) +
        1000000000000000000000000000000000000000000000000000000000000 *
          (((21 * Polynomial.X + 2) *
            (21 * Polynomial.X + 5) + 1) +
            100 * Polynomial.X + 100)

@[simp]
theorem stripEvaluatorSpacePolynomial_eval (inputLength : Nat) :
    stripEvaluatorSpacePolynomial.eval inputLength =
      stripEvaluatorSpaceBound inputLength := by
  simp [stripEvaluatorSpacePolynomial, stripEvaluatorSpaceBound,
    stripEvaluatorCoreSpaceBound, stripArithmeticSpaceBound,
    stripFuelComputationSpaceBound, stripFuelBits]

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
            stripArithmeticSpaceBound inputLength at continuationBound
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

/-- Fitted-call obligations for the four opaque primitive-recursive leaves
used by the otherwise explicit strip evaluator.  Each field is
continuation-passing: given a fitted execution after the leaf returns its
verified result, it supplies a fitted execution of the leaf call itself.

Separating this interface prevents correctness-only code selection from
silently being treated as a space bound. -/
structure StripEvaluatorLeafCallsFit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (bound : Nat) : Prop where
  base :
    ∀ first last continuation,
      first < indexCount periodicStrip →
      last < indexCount periodicStrip →
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
      EvaluatorExecutionFits bound
        (.ret continuation
          [FiniteState.divideBoolTag
            (indexedTransitionRawBool tromino periodicStrip
              first last)]) →
      EvaluatorCallFits (stripEdgeVectorCode tromino)
        continuation
        [Encodable.encode periodicStrip, first, last] bound
  stateBound :
    ∀ continuation,
      EvaluatorExecutionFits bound
        (.ret continuation [RawWindowState.stripStateBound periodicStrip]) →
      EvaluatorCallFits stripStateBoundCode continuation
        [Encodable.encode periodicStrip] bound
  wellFormed :
    ∀ continuation,
      EvaluatorExecutionFits bound
        (.ret continuation
          [FiniteState.divideBoolTag periodicStrip.wellFormed]) →
      EvaluatorCallFits stripWellFormedCode continuation
        [Encodable.encode periodicStrip] bound

end RawWindowState
end PeriodicStrip
end LeanTrominoes
