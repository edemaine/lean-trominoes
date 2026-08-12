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

/-- Replacing the original exact-fuel counter by any smaller remaining
counter preserves the common reachability-payload bound. -/
theorem stripReachCountdownPayload_encodedListSpace_le
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (first last steps remaining : Nat)
    (firstBelow : first < indexCount periodicStrip)
    (lastBelow : last < indexCount periodicStrip)
    (remainingBound :
      remaining ≤ FiniteState.divideEvalFuel
        (indexCount periodicStrip) (stripSearchDepth periodicStrip)) :
    encodedListSpace
        (remaining ::
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
  have original := stripReachPayload_encodedListSpace_le
    tromino periodicStrip first last steps firstBelow lastBelow
  have remainingBits := encodeNat_length_mono remainingBound
  simp only [encodedListSpace_cons] at original ⊢
  omega

/-- Removing the leading countdown also preserves the reachability-payload
bound. -/
theorem stripReachStatePayload_encodedListSpace_le
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (first last steps : Nat)
    (firstBelow : first < indexCount periodicStrip)
    (lastBelow : last < indexCount periodicStrip) :
    encodedListSpace
        (FiniteState.divideEvalProgramList
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
  have original := stripReachPayload_encodedListSpace_le
    tromino periodicStrip first last steps firstBelow lastBelow
  simp only [encodedListSpace_cons] at original
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

/-- Input-length envelope for one complete strip-specialized Savitch
transition. -/
def stripSavitchStepSpaceBound (inputLength : Nat) : Nat :=
  1000000000000000000000000000000 *
    (20000000 * (stripReachPayloadSpaceBound inputLength + 1) +
      stripTransitionLeafSpaceBound inputLength + 1)

noncomputable def stripSavitchStepSpacePolynomial : Polynomial Nat :=
  1000000000000000000000000000000 *
    (20000000 * (stripReachPayloadSpacePolynomial + 1) +
      stripTransitionLeafSpacePolynomial + 1)

@[simp]
theorem stripSavitchStepSpacePolynomial_eval (inputLength : Nat) :
    stripSavitchStepSpacePolynomial.eval inputLength =
      stripSavitchStepSpaceBound inputLength := by
  simp [stripSavitchStepSpacePolynomial, stripSavitchStepSpaceBound]

/-- Uniform reserve for the countdown wrapper around one Savitch step. -/
def stripSavitchBodySpaceBound (inputLength : Nat) : Nat :=
  100000 *
    (stripSavitchStepSpaceBound inputLength +
      stripReachPayloadSpaceBound inputLength + 1)

noncomputable def stripSavitchBodySpacePolynomial : Polynomial Nat :=
  100000 *
    (stripSavitchStepSpacePolynomial +
      stripReachPayloadSpacePolynomial + 1)

@[simp]
theorem stripSavitchBodySpacePolynomial_eval (inputLength : Nat) :
    stripSavitchBodySpacePolynomial.eval inputLength =
      stripSavitchBodySpaceBound inputLength := by
  simp [stripSavitchBodySpacePolynomial, stripSavitchBodySpaceBound]

/-- Workspace for assembling, running, and reading one complete indexed
reachability query.  The generous coefficient absorbs the fixed list-code
adapters surrounding the exact-fuel Savitch iterator. -/
def stripReachCallSpaceBound (inputLength : Nat) : Nat :=
  1000000 *
    (stripFuelComputationSpaceBound inputLength +
      stripLoopPayloadSpaceBound inputLength +
      stripReachPayloadSpaceBound inputLength +
      stripSavitchBodySpaceBound inputLength + 1)

noncomputable def stripReachCallSpacePolynomial : Polynomial Nat :=
  1000000 *
    (1000000000000000000000000000000000000000000000000000000000000 *
        (((21 * Polynomial.X + 2) *
          (21 * Polynomial.X + 5) + 1) +
          100 * Polynomial.X + 100) +
      stripLoopPayloadSpacePolynomial +
      stripReachPayloadSpacePolynomial +
      stripSavitchBodySpacePolynomial + 1)

@[simp]
theorem stripReachCallSpacePolynomial_eval (inputLength : Nat) :
    stripReachCallSpacePolynomial.eval inputLength =
      stripReachCallSpaceBound inputLength := by
  simp [stripReachCallSpacePolynomial, stripReachCallSpaceBound,
    stripFuelComputationSpaceBound, stripFuelBits]

/-- Workspace for one second-endpoint update: a raw edge test, a reverse
reachability call, Boolean accumulation, and fixed-width payload rebuilding. -/
def stripCandidateStepSpaceBound (inputLength : Nat) : Nat :=
  1000000000000000000 *
    (stripReachCallSpaceBound inputLength +
      stripTransitionLeafSpaceBound inputLength +
      stripLoopPayloadSpaceBound inputLength + 1)

noncomputable def stripCandidateStepSpacePolynomial : Polynomial Nat :=
  1000000000000000000 *
    (stripReachCallSpacePolynomial +
      stripTransitionLeafSpacePolynomial +
      stripLoopPayloadSpacePolynomial + 1)

@[simp]
theorem stripCandidateStepSpacePolynomial_eval (inputLength : Nat) :
    stripCandidateStepSpacePolynomial.eval inputLength =
      stripCandidateStepSpaceBound inputLength := by
  simp [stripCandidateStepSpacePolynomial, stripCandidateStepSpaceBound]

/-- Uniform reserve for the countdown wrapper around a second-endpoint
candidate update. -/
def stripCandidateBodySpaceBound (inputLength : Nat) : Nat :=
  100000 *
    (stripCandidateStepSpaceBound inputLength +
      stripLoopPayloadSpaceBound inputLength + 1)

noncomputable def stripCandidateBodySpacePolynomial : Polynomial Nat :=
  100000 *
    (stripCandidateStepSpacePolynomial +
      stripLoopPayloadSpacePolynomial + 1)

@[simp]
theorem stripCandidateBodySpacePolynomial_eval (inputLength : Nat) :
    stripCandidateBodySpacePolynomial.eval inputLength =
      stripCandidateBodySpaceBound inputLength := by
  simp [stripCandidateBodySpacePolynomial, stripCandidateBodySpaceBound]

/-- One common polynomial envelope for search payloads and explicit
search-depth and fuel arithmetic. -/
def stripEvaluatorSpaceBound (inputLength : Nat) : Nat :=
  stripEvaluatorCoreSpaceBound inputLength +
    stripArithmeticSpaceBound inputLength +
      stripStateBoundComputationSpaceBound inputLength +
          stripFuelComputationSpaceBound inputLength +
          stripTransitionLeafSpaceBound inputLength +
            stripSavitchBodySpaceBound inputLength +
              stripReachCallSpaceBound inputLength +
                stripCandidateStepSpaceBound inputLength +
                  stripCandidateBodySpaceBound inputLength

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
            stripTransitionLeafSpacePolynomial +
              stripSavitchBodySpacePolynomial +
                stripReachCallSpacePolynomial +
                  stripCandidateStepSpacePolynomial +
                    stripCandidateBodySpacePolynomial

@[simp]
theorem stripEvaluatorSpacePolynomial_eval (inputLength : Nat) :
    stripEvaluatorSpacePolynomial.eval inputLength =
      stripEvaluatorSpaceBound inputLength := by
  simp [stripEvaluatorSpacePolynomial, stripEvaluatorSpaceBound,
    stripEvaluatorCoreSpaceBound, stripArithmeticSpaceBound,
    stripStateBoundComputationSpaceBound,
    stripFuelComputationSpaceBound, stripTransitionLeafSpaceBound,
    stripSavitchBodySpaceBound, stripSavitchStepSpaceBound,
    stripReachCallSpaceBound, stripCandidateStepSpaceBound,
    stripCandidateBodySpaceBound, stripFuelBits]

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

namespace StripSavitchStep

open Turing.PartrecToTM2.EvaluatorCodeFits

def baseArgumentsCost
    (context stateCount : Nat) (state : FiniteState.DivideEvalState) : Nat :=
  let values := FiniteState.divideEvalProgramList context stateCount state
  let last := prependCost values [state.query.last] []
    (getCost 6 values) (nilCost values)
  let first := prependCost values [state.query.first] [state.query.last]
    (getCost 5 values) last
  prependCost values [context] [state.query.first, state.query.last]
    (getCost 0 values) first

theorem baseArguments
    (context stateCount : Nat) (state : FiniteState.DivideEvalState) :
    Turing.PartrecToTM2.EvaluatorCodeFits
      LeanTrominoes.PeriodicStrip.RawWindowState.stripBaseArguments
      (FiniteState.divideEvalProgramList context stateCount state)
      [context, state.query.first, state.query.last]
      (baseArgumentsCost context stateCount state) := by
  let values := FiniteState.divideEvalProgramList context stateCount state
  have last := prepend (get 6 values) (nil values)
  have first := prepend (get 5 values) last
  have result := prepend (get 0 values) first
  simpa [LeanTrominoes.PeriodicStrip.RawWindowState.stripBaseArguments,
    baseArgumentsCost, values,
    FiniteState.divideEvalProgramList,
    FiniteState.DivideEvalState.toNatList, prependCost] using result

def baseBoolCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (stateCount : Nat) (state : FiniteState.DivideEvalState) : Nat :=
  Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionCost
      tromino periodicStrip state.query.first state.query.last +
    baseArgumentsCost (Encodable.encode periodicStrip) stateCount state

theorem baseBool
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount : Nat) (state : FiniteState.DivideEvalState) :
    Turing.PartrecToTM2.EvaluatorCodeFits
      (stripBaseBoolCode tromino)
      (FiniteState.divideEvalProgramList
        (Encodable.encode periodicStrip) stateCount state)
      [FiniteState.divideBoolTag
        (decide (state.query.first = state.query.last) ||
          indexedTransitionRawBool tromino periodicStrip
            state.query.first state.query.last)]
      (baseBoolCost tromino periodicStrip stateCount state) := by
  let leaf :=
    Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransition
      tromino periodicStrip wellFormed
      state.query.first state.query.last
  have result := Turing.PartrecToTM2.EvaluatorCodeFits.comp leaf
    (StripSavitchStep.baseArguments
      (Encodable.encode periodicStrip) stateCount state)
  cases answer :
      (decide (state.query.first = state.query.last) ||
        indexedTransitionRawBool tromino periodicStrip
          state.query.first state.query.last) <;>
    simpa [stripBaseBoolCode, baseBoolCost,
      stripBaseVectorCode, answer, FiniteState.divideBoolTag] using result

/-- A shared local unit for the structural step: its serialized input, its
only non-structural leaf, and one slack cell. -/
def stepSpaceUnit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (stateCount : Nat) (state : FiniteState.DivideEvalState) : Nat :=
  encodedListSpace
      (FiniteState.divideEvalProgramList
        (Encodable.encode periodicStrip) stateCount state) +
    baseBoolCost tromino periodicStrip stateCount state + 1

/-- Generous fixed coefficient absorbing every constructor in one compiled
Savitch transition. -/
def stepCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (stateCount : Nat) (state : FiniteState.DivideEvalState) : Nat :=
  1000000000000000000000000000000 *
    stepSpaceUnit tromino periodicStrip stateCount state

def someBoolTagCost
    (values : List Nat) (result valueCost : Nat) : Nat :=
  succCost [if result = 0 then 0 else 1] +
    normalizeBoolCost values result valueCost

theorem someBoolTag
    {value : Turing.ToPartrec.Code} {values : List Nat}
    {result valueCost : Nat}
    (valueFits :
      Turing.PartrecToTM2.EvaluatorCodeFits value values [result] valueCost) :
    Turing.PartrecToTM2.EvaluatorCodeFits
      (Turing.ToPartrec.Code.someBoolTag value) values
      [if result = 0 then 1 else 2]
      (someBoolTagCost values result valueCost) := by
  have normalized := normalizeBool valueFits
  have incremented := Turing.PartrecToTM2.EvaluatorCodeFits.comp
    (succ_named [if result = 0 then 0 else 1]) normalized
  by_cases zero : result = 0 <;>
    simp [Turing.ToPartrec.Code.someBoolTag, someBoolTagCost,
      zero] at incremented ⊢ <;>
    exact incremented

private theorem idCost_le_linear (values : List Nat) :
    idCost values ≤ 10 * (encodedListSpace values + 1) := by
  have tailSpace := listCodeEncodedListSpace_tail_le (0 :: values)
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  simp [idCost, tailCost, zeroPrimeCost,
    encodedListSpace_cons, zeroBits] at tailSpace ⊢
  omega

private theorem encodedListSpace_cons_le_of
    (value : Nat) (values : List Nat) (budget : Nat)
    (valueBound : encodedListSpace [value] ≤ budget)
    (valuesBound : encodedListSpace values ≤ budget) :
    encodedListSpace (value :: values) ≤ 2 * budget := by
  rw [show value :: values = [value] ++ values by rfl,
    FiniteState.encodedListSpace_append]
  omega

private theorem predecessorSingletonSpace_le (value : Nat) :
    encodedListSpace [value.pred] ≤ encodedListSpace [value] := by
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  exact Nat.add_le_add_right
    (listCodeEncodeNat_length_mono (Nat.pred_le value)) 1

private theorem singletonGetDSpace_le
    (index : Nat) (values : List Nat) :
    encodedListSpace [values[index]?.getD 0] ≤
      encodedListSpace values + 1 := by
  induction index generalizing values with
  | zero =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [List.getElem?_cons_zero, Option.getD_some,
            List.headI_cons] at *
          exact encodedListSpace_singleton_headI_le (value :: values)
  | succ index induction =>
      cases values with
      | nil => rfl
      | cons value values =>
          have tail := induction values
          simp only [List.getElem?_cons_succ, Option.getD_some] at tail ⊢
          exact tail.trans (Nat.add_le_add_right
            (listCodeEncodedListSpace_tail_le (value :: values)) 1)

private theorem dropCost_le_linear (index : Nat) (values : List Nat) :
    dropCost index values ≤
      (10000 * (index + 1)) * (encodedListSpace values + 1) := by
  have whole := listCodeGetCost_le_linear index values
  have part : dropCost index values ≤ getCost index values := by
    simp only [getCost]
    omega
  exact part.trans whole

private theorem nilCost_le_linear (values : List Nat) :
    nilCost values ≤ 1000 * (encodedListSpace values + 1) := by
  have headSpace := encodedListSpace_singleton_headI_le values
  have successorBits := encodeNat_succ_length_le values.headI
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  simp [nilCost, tailCost, succCost, encodedListSpace_cons,
    zeroBits] at headSpace successorBits ⊢
  omega

private theorem oneCost_le_linear (values : List Nat) :
    oneCost values ≤ 20000 * (encodedListSpace values + 1) := by
  have zeroBound := listCodeZeroCost_le_linear values
  have successor := succCost_le [0]
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  simp only [oneCost]
  simp [encodedListSpace_cons, zeroBits] at successor
  omega

private theorem getCost_le_budget
    (index : Nat) (values : List Nat) (budget : Nat)
    (indexBound : index ≤ 12)
    (valuesBound : encodedListSpace values ≤ budget) :
    getCost index values ≤ 130000 * (budget + 1) := by
  calc
    getCost index values ≤
        (10000 * (index + 1)) * (encodedListSpace values + 1) :=
      listCodeGetCost_le_linear index values
    _ ≤ (10000 * 13) * (budget + 1) := by
      gcongr
      omega
    _ = 130000 * (budget + 1) := by ring

private theorem dropCost_le_budget
    (index : Nat) (values : List Nat) (budget : Nat)
    (indexBound : index ≤ 12)
    (valuesBound : encodedListSpace values ≤ budget) :
    dropCost index values ≤ 130000 * (budget + 1) := by
  exact (dropCost_le_linear index values).trans (by
    gcongr
    omega)

private theorem idCost_le_budget
    (values : List Nat) (budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget) :
    idCost values ≤ 10 * (budget + 1) :=
  (idCost_le_linear values).trans (by gcongr)

private theorem zeroCost_le_budget
    (values : List Nat) (budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget) :
    zeroCost values ≤ 10000 * (budget + 1) :=
  (listCodeZeroCost_le_linear values).trans (by gcongr)

private theorem oneCost_le_budget
    (values : List Nat) (budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget) :
    oneCost values ≤ 20000 * (budget + 1) :=
  (oneCost_le_linear values).trans (by gcongr)

private theorem scaledFieldSpace_le
    (value : Nat) :
    encodedListSpace [2 * value + 4] ≤
      10 * (encodedListSpace [value] + 1) := by
  have product := encodeNat_mul_length_le_sum 2 value
  have sum := encodeNat_add_length_le_sum (2 * value) 4
  have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
  have fourBits : (Computability.encodeNat 4).length = 3 := by native_decide
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  rw [twoBits] at product
  rw [fourBits] at sum
  omega

private theorem branchZeroZeroCost_le_budget
    (values output : List Nat) (testValue testCost branchCost budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget)
    (outputBound : encodedListSpace output ≤ budget)
    (testValueBound : encodedListSpace [testValue] ≤ budget)
    (testCostBound : testCost ≤ budget)
    (branchCostBound : branchCost ≤ budget) :
    branchZeroZeroCost values output testValue testCost branchCost ≤
      40 * (budget + 1) := by
  have testedInput := encodedListSpace_cons_le_of
    testValue values budget testValueBound valuesBound
  have identity := idCost_le_linear values
  have testHead : [testValue].headI = testValue := by simp
  simp only [branchZeroZeroCost, branchZeroTestCost, prependCost]
  rw [testHead]
  omega

private theorem branchZeroSuccCost_le_budget
    (values output : List Nat) (testValue testCost branchCost budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget)
    (outputBound : encodedListSpace output ≤ budget)
    (testValueBound : encodedListSpace [testValue] ≤ budget)
    (testCostBound : testCost ≤ budget)
    (branchCostBound : branchCost ≤ budget) :
    branchZeroSuccCost values output testValue testCost branchCost ≤
      50 * (budget + 1) := by
  have testedInput := encodedListSpace_cons_le_of
    testValue values budget testValueBound valuesBound
  have predecessorBound := predecessorSingletonSpace_le testValue
  have predecessorInput := encodedListSpace_cons_le_of
    testValue.pred values budget (predecessorBound.trans testValueBound)
      valuesBound
  have identity := idCost_le_linear values
  have tail := listCodeTailCost_le_linear (testValue.pred :: values)
  have testHead : [testValue].headI = testValue := by simp
  simp only [branchZeroSuccCost, branchZeroTestCost, prependCost]
  rw [testHead]
  omega

set_option maxRecDepth 100000 in
private theorem normalizeBoolCost_le_budget
    (values : List Nat) (result valueCost budget : Nat)
    (resultBound : result ≤ 1)
    (valuesBound : encodedListSpace values ≤ budget)
    (valueCostBound : valueCost ≤ budget)
    (positive : 1 ≤ budget) :
    normalizeBoolCost values result valueCost ≤
      2000000 * (budget + 1) := by
  have zeroSpace : encodedListSpace [0] ≤ 2 * (budget + 1) := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    simp only [encodedListSpace_cons, encodedListSpace_nil, zeroBits,
      Nat.zero_add]
    omega
  have oneSpace : encodedListSpace [1] ≤ 2 * (budget + 1) := by
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    simp [encodedListSpace_cons, oneBits]
  have valuesLarge : encodedListSpace values ≤ 2 * (budget + 1) := by omega
  have valueCostLarge : valueCost ≤ 2 * (budget + 1) := by omega
  have zeroCostLarge : zeroCost values ≤ 2 * (10000 * (budget + 1)) := by
    have bound := listCodeZeroCost_le_linear values
    calc
      zeroCost values ≤ 10000 * (encodedListSpace values + 1) := bound
      _ ≤ 10000 * (budget + 1) := by gcongr
      _ ≤ 2 * (10000 * (budget + 1)) := by omega
  have oneCostLarge : oneCost values ≤ 2 * (10000 * (budget + 1)) := by
    have zeroBound := listCodeZeroCost_le_linear values
    have successor := succCost_le [0]
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    simp only [oneCost]
    simp [encodedListSpace_cons, zeroBits] at successor
    omega
  rcases (show result = 0 ∨ result = 1 by omega) with rfl | rfl
  · simp only [normalizeBoolCost, if_pos]
    exact (branchZeroZeroCost_le_budget values [0] 0 valueCost
      (zeroCost values) (2 * (10000 * (budget + 1)))
      (by omega) (by omega) (by omega) (by omega) zeroCostLarge).trans
        (by omega)
  · simp only [normalizeBoolCost, if_neg (by decide : (1 : Nat) ≠ 0)]
    exact (branchZeroSuccCost_le_budget values [1] 1 valueCost
      (oneCost values) (2 * (10000 * (budget + 1)))
      (by omega) (by omega) (by omega) (by omega) oneCostLarge).trans
        (by omega)

private theorem someBoolTagCost_le_budget
    (values : List Nat) (result valueCost budget : Nat)
    (resultBound : result ≤ 1)
    (valuesBound : encodedListSpace values ≤ budget)
    (valueCostBound : valueCost ≤ budget)
    (positive : 1 ≤ budget) :
    someBoolTagCost values result valueCost ≤
      100000000 * (budget + 1) := by
  have normalized := normalizeBoolCost_le_budget values result valueCost budget
    resultBound valuesBound valueCostBound positive
  have normalizedValue : (if result = 0 then 0 else 1) ≤ 1 := by
    split <;> omega
  have normalizedSpace :
      encodedListSpace [if result = 0 then 0 else 1] ≤ budget + 2 := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    split <;> simp [encodedListSpace_cons, zeroBits, oneBits]
  have successor := succCost_le [if result = 0 then 0 else 1]
  simp only [someBoolTagCost]
  omega

structure FieldFit (values : List Nat) where
  code : Turing.ToPartrec.Code
  output : Nat
  cost : Nat
  fits : Turing.PartrecToTM2.EvaluatorCodeFits code values [output] cost

def fieldsCost (values : List Nat) :
    List (FieldFit values) → List Nat → Nat → Nat
  | [], _, restCost => restCost
  | field :: fields, restOutput, restCost =>
      prependCost values [field.output]
        (fields.map FieldFit.output ++ restOutput)
        field.cost (fieldsCost values fields restOutput restCost)

theorem fields
    (values : List Nat) (fieldFits : List (FieldFit values))
    {restCode : Turing.ToPartrec.Code}
    {restOutput : List Nat} {restCost : Nat}
    (restFits :
      Turing.PartrecToTM2.EvaluatorCodeFits
        restCode values restOutput restCost) :
    Turing.PartrecToTM2.EvaluatorCodeFits
      (FiniteState.DivideEvalPartrec.fields
        (fieldFits.map FieldFit.code) restCode)
      values (fieldFits.map FieldFit.output ++ restOutput)
      (fieldsCost values fieldFits restOutput restCost) := by
  induction fieldFits with
  | nil => simpa [FiniteState.DivideEvalPartrec.fields, fieldsCost] using restFits
  | cons field fieldFits induction =>
      have combined := prepend field.fits induction
      simpa [FiniteState.DivideEvalPartrec.fields, fieldsCost,
        prependCost] using combined

set_option maxHeartbeats 10000 in
/-- A list of fitted fields can be assembled without re-expanding every
nested prepend node: only the child costs, the number of fields, and a common
bound on the input and assembled-output footprints matter. -/
theorem fieldsCost_le_of
    (values : List Nat) (fieldFits : List (FieldFit values))
    (restOutput : List Nat) (restCost unit : Nat)
    (valuesBound : encodedListSpace values ≤ unit)
    (outputBound :
      encodedListSpace (fieldFits.map FieldFit.output ++ restOutput) ≤ unit) :
    fieldsCost values fieldFits restOutput restCost ≤
      restCost + (fieldFits.map FieldFit.cost).sum +
        fieldFits.length * (3 * (unit + 2) + 2) := by
  induction fieldFits with
  | nil => simp [fieldsCost]
  | cons field fieldFits induction =>
      let tailOutput := fieldFits.map FieldFit.output ++ restOutput
      have tailSpace : encodedListSpace tailOutput ≤ unit := by
        have tail := listCodeEncodedListSpace_tail_le
          (field.output :: tailOutput)
        exact tail.trans (by
          simpa [tailOutput] using outputBound)
      have fieldSpace : encodedListSpace [field.output] ≤ unit + 1 := by
        have head := encodedListSpace_singleton_headI_le
          (field.output :: tailOutput)
        exact head.trans (Nat.add_le_add_right
          (by simpa [tailOutput] using outputBound) 1)
      have combinedSpace :
          encodedListSpace (field.output :: tailOutput) ≤ unit + 1 := by
        have currentSpace :
            encodedListSpace (field.output :: tailOutput) ≤ unit := by
          simpa [tailOutput] using outputBound
        exact currentSpace.trans (Nat.le_succ unit)
      have prepend := EvaluatorCodeFits.listCodePrependCost_le_of
        values [field.output] tailOutput field.cost
        (fieldsCost values fieldFits restOutput restCost) (unit + 1)
        (valuesBound.trans (Nat.le_succ unit)) fieldSpace
        (by simpa using combinedSpace)
      have rest := induction tailSpace
      simp only [fieldsCost]
      apply prepend.trans
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, one_mul]
      omega

def getField (index : Nat) (values : List Nat) : FieldFit values where
  code := FiniteState.DivideEvalPartrec.field index
  output := values[index]?.getD 0
  cost := getCost index values
  fits := by
    simpa [FiniteState.DivideEvalPartrec.field] using get index values

def predecessorField (index : Nat) (values : List Nat) : FieldFit values where
  code := FiniteState.DivideEvalPartrec.predecessorField index
  output := (values[index]?.getD 0).pred
  cost := predCost [values[index]?.getD 0] + getCost index values
  fits := by
    have result := Turing.PartrecToTM2.EvaluatorCodeFits.comp
      (pred_named [values[index]?.getD 0]) (get index values)
    simpa [FiniteState.DivideEvalPartrec.predecessorField,
      FiniteState.DivideEvalPartrec.field,
      Turing.ToPartrec.Code.subtractStepList] using result

@[simp]
theorem getField_cost (index : Nat) (values : List Nat) :
    (getField index values).cost = getCost index values := rfl

@[simp]
theorem predecessorField_cost (index : Nat) (values : List Nat) :
    (predecessorField index values).cost =
      predCost [values[index]?.getD 0] + getCost index values := rfl

def zeroField (values : List Nat) : FieldFit values where
  code := Turing.ToPartrec.Code.zero
  output := 0
  cost := zeroCost values
  fits := zero values

def oneField (values : List Nat) : FieldFit values where
  code := Turing.ToPartrec.Code.one
  output := 1
  cost := oneCost values
  fits := one values

def succField (index : Nat) (values : List Nat) : FieldFit values where
  code := Turing.ToPartrec.Code.succ.comp
    (FiniteState.DivideEvalPartrec.field index)
  output := (values[index]?.getD 0).succ
  cost := succCost [values[index]?.getD 0] + getCost index values
  fits := by
    have result := Turing.PartrecToTM2.EvaluatorCodeFits.comp
      (succ_named [values[index]?.getD 0]) (get index values)
    simpa [FiniteState.DivideEvalPartrec.field] using result

def someBoolField
    (values : List Nat) (valueCode : Turing.ToPartrec.Code)
    (result valueCost : Nat)
    (valueFits :
      Turing.PartrecToTM2.EvaluatorCodeFits
        valueCode values [result] valueCost) : FieldFit values where
  code := Turing.ToPartrec.Code.someBoolTag valueCode
  output := if result = 0 then 1 else 2
  cost := someBoolTagCost values result valueCost
  fits := someBoolTag valueFits

private theorem successorFieldCost_le_budget
    (index : Nat) (values : List Nat) (budget : Nat)
    (indexBound : index ≤ 12)
    (valuesBound : encodedListSpace values ≤ budget) :
    (succField index values).cost ≤ 1000000 * (budget + 1) := by
  have projected := singletonGetDSpace_le index values
  have successor := succCost_le [values[index]?.getD 0]
  have projection := getCost_le_budget index values budget indexBound valuesBound
  simp only [succField]
  omega

private theorem predecessorFieldCost_le_budget
    (index : Nat) (values : List Nat) (budget : Nat)
    (indexBound : index ≤ 12)
    (valuesBound : encodedListSpace values ≤ budget) :
    (predecessorField index values).cost ≤
      30000000 * (budget + 1) := by
  let value := values[index]?.getD 0
  have projected := singletonGetDSpace_le index values
  have scaled := scaledFieldSpace_le value
  have predecessor := predCost_singleton_le_linear value
  have projection := getCost_le_budget index values budget indexBound valuesBound
  dsimp only [value] at projected scaled predecessor ⊢
  simp only [predecessorField]
  omega

/-- The fixed three-field adapter feeding the base leaf is linear in the
serialized DFS state. -/
theorem baseArgumentsCost_le_linear
    (context stateCount : Nat) (state : FiniteState.DivideEvalState) :
    baseArgumentsCost context stateCount state ≤
      10000000 *
        (encodedListSpace
          (FiniteState.divideEvalProgramList context stateCount state) + 1) := by
  let values := FiniteState.divideEvalProgramList context stateCount state
  let budget := encodedListSpace values
  have valuesBound : encodedListSpace values ≤ budget := Nat.le_refl _
  have get0 := getCost_le_budget 0 values budget (by omega) valuesBound
  have get5 := getCost_le_budget 5 values budget (by omega) valuesBound
  have get6 := getCost_le_budget 6 values budget (by omega) valuesBound
  have nil := nilCost_le_linear values
  have field0 := singletonGetDSpace_le 0 values
  have field5 := singletonGetDSpace_le 5 values
  have field6 := singletonGetDSpace_le 6 values
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  simp [baseArgumentsCost, prependCost, values, budget,
    FiniteState.divideEvalProgramList,
    FiniteState.DivideEvalState.toNatList,
    FiniteState.divideOptionBoolTag, zeroBits]
    at get0 get5 get6 nil field0 field5 field6 ⊢
  omega

private def accumulatedRawBudget (budget : Nat) : Nat :=
  1000 * (1000 * (60000000 * (budget + 1) + 1) + 1)

private def accumulatedTagBudget (budget : Nat) : Nat :=
  100000000 * (accumulatedRawBudget budget + 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem accumulatedRawCost_le_budget
    (values : List Nat)
    (accumulatedValue leftValue rightValue : Nat)
    (accumulatedCost leftCost rightCost budget : Nat)
    (accumulatedValueBound : accumulatedValue ≤ 1)
    (leftValueBound : leftValue ≤ 1)
    (rightValueBound : rightValue ≤ 1)
    (valuesBound : encodedListSpace values ≤ budget)
    (accumulatedCostBound : accumulatedCost ≤ 130000 * (budget + 1))
    (leftCostBound : leftCost ≤ 30000000 * (budget + 1))
    (rightCostBound : rightCost ≤ 30000000 * (budget + 1)) :
    boolOrCost values accumulatedValue
        (if leftValue = 0 ∨ rightValue = 0 then 0 else 1)
        accumulatedCost
        (boolAndCost values leftValue rightValue leftCost rightCost) ≤
      accumulatedRawBudget budget := by
  have headSpace := encodedListSpace_singleton_headI_le values
  have headBitsInput :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have headSuccessorInput := encodeNat_succ_length_le values.headI
  let firstBudget := 60000000 * (budget + 1)
  have firstPositive : 1 ≤ firstBudget := by
    dsimp only [firstBudget]
    omega
  have firstValues : encodedListSpace values ≤ firstBudget := by
    dsimp only [firstBudget]
    omega
  have firstHead :
      (Computability.encodeNat values.headI).length ≤ firstBudget := by
    dsimp only [firstBudget]
    omega
  have firstHeadSuccessor :
      (Computability.encodeNat (values.headI + 1)).length ≤ firstBudget := by
    simp only [Nat.succ_eq_add_one] at headSuccessorInput
    dsimp only [firstBudget]
    omega
  have firstLeft : leftCost ≤ firstBudget := by
    dsimp only [firstBudget]
    omega
  have firstRight : rightCost ≤ firstBudget := by
    dsimp only [firstBudget]
    omega
  have both := boolAndCost_le_budget values leftValue rightValue
    leftCost rightCost firstBudget leftValueBound rightValueBound
    firstValues firstHead firstHeadSuccessor firstLeft firstRight firstPositive
  let secondBudget := 1000 * (firstBudget + 1)
  have firstSecond : firstBudget ≤ secondBudget := by
    dsimp only [secondBudget]
    omega
  have secondPositive : 1 ≤ secondBudget := by
    exact firstPositive.trans firstSecond
  have secondValues : encodedListSpace values ≤ secondBudget :=
    firstValues.trans firstSecond
  have secondHead :
      (Computability.encodeNat values.headI).length ≤ secondBudget := by
    exact firstHead.trans firstSecond
  have secondHeadSuccessor :
      (Computability.encodeNat (values.headI + 1)).length ≤ secondBudget := by
    exact firstHeadSuccessor.trans firstSecond
  have firstAccumulated : accumulatedCost ≤ firstBudget := by
    dsimp only [firstBudget]
    omega
  have secondAccumulated : accumulatedCost ≤ secondBudget :=
    firstAccumulated.trans firstSecond
  have secondBoth :
      boolAndCost values leftValue rightValue leftCost rightCost ≤
        secondBudget := by
    simpa [secondBudget] using both
  have bothValueBound :
      (if leftValue = 0 ∨ rightValue = 0 then 0 else 1) ≤ 1 := by
    split <;> omega
  have combined := boolOrCost_le_budget values accumulatedValue
    (if leftValue = 0 ∨ rightValue = 0 then 0 else 1)
    accumulatedCost
    (boolAndCost values leftValue rightValue leftCost rightCost)
    secondBudget accumulatedValueBound bothValueBound secondValues
    secondHead secondHeadSuccessor secondAccumulated secondBoth secondPositive
  simpa [accumulatedRawBudget, secondBudget, firstBudget] using combined

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem accumulatedTagCost_le_budget
    (values : List Nat)
    (result accumulatedValue leftValue rightValue : Nat)
    (accumulatedCost leftCost rightCost budget : Nat)
    (resultBound : result ≤ 1)
    (accumulatedValueBound : accumulatedValue ≤ 1)
    (leftValueBound : leftValue ≤ 1)
    (rightValueBound : rightValue ≤ 1)
    (valuesBound : encodedListSpace values ≤ budget)
    (accumulatedCostBound : accumulatedCost ≤ 130000 * (budget + 1))
    (leftCostBound : leftCost ≤ 30000000 * (budget + 1))
    (rightCostBound : rightCost ≤ 30000000 * (budget + 1)) :
    someBoolTagCost values result
        (boolOrCost values accumulatedValue
          (if leftValue = 0 ∨ rightValue = 0 then 0 else 1)
          accumulatedCost
          (boolAndCost values leftValue rightValue leftCost rightCost)) ≤
      accumulatedTagBudget budget := by
  have raw := accumulatedRawCost_le_budget values accumulatedValue
    leftValue rightValue accumulatedCost leftCost rightCost budget
    accumulatedValueBound leftValueBound rightValueBound valuesBound
    accumulatedCostBound leftCostBound rightCostBound
  let tagBudget := accumulatedRawBudget budget
  have tagPositive : 1 ≤ tagBudget := by
    dsimp only [tagBudget, accumulatedRawBudget]
    omega
  have tagValues : encodedListSpace values ≤ tagBudget := by
    dsimp only [tagBudget, accumulatedRawBudget]
    omega
  have tagged := someBoolTagCost_le_budget values result
    (boolOrCost values accumulatedValue
      (if leftValue = 0 ∨ rightValue = 0 then 0 else 1)
      accumulatedCost
      (boolAndCost values leftValue rightValue leftCost rightCost))
    tagBudget resultBound tagValues (by simpa [tagBudget] using raw) tagPositive
  simpa [accumulatedTagBudget, tagBudget] using tagged

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Every semantic branch of the strip-specialized Savitch transition has a
compositional evaluator-space certificate at one common structural cost. -/
theorem exactStep
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount : Nat) (state : FiniteState.DivideEvalState) :
    Turing.PartrecToTM2.EvaluatorCodeFits
        (FiniteState.DivideEvalPartrec.stepCode
          (stripBaseBoolCode tromino))
        (FiniteState.divideEvalProgramList
          (Encodable.encode periodicStrip) stateCount state)
        (FiniteState.divideEvalProgramList
          (Encodable.encode periodicStrip) stateCount
          (FiniteState.divideEvalStep stateCount
            (indexedTransitionRawBool tromino periodicStrip) state))
        (stepCost tromino periodicStrip stateCount state) := by
  cases state with
  | mk query stack answer =>
    cases query with
    | mk depth first last =>
      let values :=
        FiniteState.divideEvalProgramList
          (Encodable.encode periodicStrip) stateCount
          { query := { depth := depth, first := first, last := last },
            stack := stack, answer := answer }
      cases answer with
      | none =>
        cases depth with
        | zero =>
          let state : FiniteState.DivideEvalState :=
            { query := { depth := 0, first := first, last := last },
              stack := stack, answer := none }
          have base := baseBool tromino periodicStrip wellFormed stateCount state
          let baseResult :=
            FiniteState.divideBoolTag
              (decide (first = last) ||
                indexedTransitionRawBool tromino periodicStrip first last)
          let tag := someBoolField values
            (stripBaseBoolCode tromino) baseResult
            (baseBoolCost tromino periodicStrip stateCount state)
            (by simpa [values, state, baseResult] using base)
          let fieldFits : List (FieldFit values) :=
            [getField 0 values, getField 1 values, getField 2 values, tag,
              getField 4 values, getField 5 values, getField 6 values]
          have branch := fields values fieldFits (drop 7 values)
          have depthBranch := branchZero_zero
            (whenSucc := FiniteState.DivideEvalPartrec.noneDepthSucc)
            (testValue := 0) rfl
            (get 4 values) (by simpa [values, state, fieldFits, tag] using branch)
          have whole := branchZero_zero
            (whenSucc := FiniteState.DivideEvalPartrec.answerSome)
            (testValue := 0) rfl
            (get 3 values) depthBranch
          let unit := stepSpaceUnit tromino periodicStrip stateCount state
          have valuesBound : encodedListSpace values ≤ unit := by
            simp [unit, stepSpaceUnit, values, state]
            omega
          have baseCostBound :
              baseBoolCost tromino periodicStrip stateCount state ≤ unit := by
            simp [unit, stepSpaceUnit]
            omega
          have unitPositive : 1 ≤ unit := by
            simp [unit, stepSpaceUnit]
          have baseResultBound : baseResult ≤ 1 := by
            cases result :
                (decide (first = last) ||
                  indexedTransitionRawBool tromino periodicStrip first last) <;>
              simp [baseResult, result, FiniteState.divideBoolTag]
          have tagCostBound : tag.cost ≤ 100000000 * (unit + 1) := by
            simpa [tag, someBoolField] using
              someBoolTagCost_le_budget values baseResult
                (baseBoolCost tromino periodicStrip stateCount state) unit
                baseResultBound valuesBound baseCostBound unitPositive
          dsimp [tag, someBoolField] at tagCostBound
          have get0 := listCodeGetCost_le_linear 0 values
          have get1 := listCodeGetCost_le_linear 1 values
          have get2 := listCodeGetCost_le_linear 2 values
          have get3 := listCodeGetCost_le_linear 3 values
          have get4 := listCodeGetCost_le_linear 4 values
          have get5 := listCodeGetCost_le_linear 5 values
          have get6 := listCodeGetCost_le_linear 6 values
          have drop7 := dropCost_le_linear 7 values
          have identity := idCost_le_linear values
          have get0Bound : getCost 0 values ≤ 10000 * (unit + 1) :=
            get0.trans (by gcongr)
          have get1Bound : getCost 1 values ≤ 20000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get1.trans (Nat.mul_le_mul_left 20000
                (Nat.add_le_add_right valuesBound 1))
          have get2Bound : getCost 2 values ≤ 30000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get2.trans (Nat.mul_le_mul_left 30000
                (Nat.add_le_add_right valuesBound 1))
          have get3Bound : getCost 3 values ≤ 40000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get3.trans (Nat.mul_le_mul_left 40000
                (Nat.add_le_add_right valuesBound 1))
          have get4Bound : getCost 4 values ≤ 50000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get4.trans (Nat.mul_le_mul_left 50000
                (Nat.add_le_add_right valuesBound 1))
          have get5Bound : getCost 5 values ≤ 60000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get5.trans (Nat.mul_le_mul_left 60000
                (Nat.add_le_add_right valuesBound 1))
          have get6Bound : getCost 6 values ≤ 70000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get6.trans (Nat.mul_le_mul_left 70000
                (Nat.add_le_add_right valuesBound 1))
          have drop7Bound : dropCost 7 values ≤ 80000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              drop7.trans (Nat.mul_le_mul_left 80000
                (Nat.add_le_add_right valuesBound 1))
          have identityBound : idCost values ≤ 10 * (unit + 1) :=
            identity.trans (Nat.mul_le_mul_left 10
              (Nat.add_le_add_right valuesBound 1))
          have explicitValuesBound := valuesBound
          have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
          have oneBits : (Computability.encodeNat 1).length = 1 := rfl
          have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
          cases baseAnswer :
              (decide (first = last) ||
                indexedTransitionRawBool tromino periodicStrip first last)
          all_goals
            apply Turing.PartrecToTM2.EvaluatorCodeFits.mono
            · simpa [FiniteState.DivideEvalPartrec.stepCode,
                FiniteState.DivideEvalPartrec.answerNone,
                FiniteState.DivideEvalPartrec.noneDepthZero,
                FiniteState.DivideEvalPartrec.field,
                FiniteState.DivideEvalPartrec.fields,
                FiniteState.divideEvalProgramList,
                FiniteState.DivideEvalState.toNatList,
                FiniteState.divideEvalStep, values, state, fieldFits, tag,
                baseResult, baseAnswer, getField, someBoolField,
                FiniteState.divideBoolTag,
                FiniteState.divideOptionBoolTag] using whole
            · rw [show stepCost tromino periodicStrip stateCount state =
                  1000000000000000000000000000000 * unit by rfl]
              simp [fieldsCost,
                branchZeroZeroCost, branchZeroTestCost, prependCost,
                baseResult, baseAnswer, values, state,
                getField, someBoolField,
                FiniteState.divideEvalProgramList,
                FiniteState.DivideEvalState.toNatList,
                FiniteState.divideOptionBoolTag,
                FiniteState.divideBoolTag,
                zeroBits, oneBits, twoBits] at tagCostBound get0Bound get1Bound get2Bound get3Bound get4Bound get5Bound get6Bound drop7Bound identityBound explicitValuesBound ⊢
              omega
        | succ depth =>
          cases stateCount with
          | zero =>
            let state : FiniteState.DivideEvalState :=
              { query := { depth := depth + 1, first := first, last := last },
                stack := stack, answer := none }
            let fieldFits : List (FieldFit values) :=
              [getField 0 values, getField 1 values, getField 2 values,
                oneField values, getField 4 values, getField 5 values,
                getField 6 values]
            have countBranch := fields values fieldFits (drop 7 values)
            have depthBranch := branchZero_zero
              (whenSucc := FiniteState.DivideEvalPartrec.noneCountSucc)
              (testValue := 0) rfl
              (get 1 values)
              (by simpa [values, state, fieldFits] using countBranch)
            have answerBranch := branchZero_succ
              (whenZero := FiniteState.DivideEvalPartrec.noneDepthZero
                (stripBaseBoolCode tromino))
              (testValue := depth + 1)
              (by omega) (get 4 values)
              (by simpa [values, state] using depthBranch)
            have whole := branchZero_zero
              (whenSucc := FiniteState.DivideEvalPartrec.answerSome)
              (testValue := 0) rfl
              (get 3 values) answerBranch
            have wholeFits := (by
              simpa [FiniteState.DivideEvalPartrec.stepCode,
              FiniteState.DivideEvalPartrec.answerNone,
              FiniteState.DivideEvalPartrec.noneDepthSucc,
              FiniteState.DivideEvalPartrec.noneCountZero,
              FiniteState.DivideEvalPartrec.field,
              FiniteState.DivideEvalPartrec.fields,
              FiniteState.divideEvalProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.divideEvalStep, values, state, fieldFits,
              getField, oneField,
              FiniteState.divideOptionBoolTag] using whole)
            apply wholeFits.mono
            let unit := stepSpaceUnit tromino periodicStrip 0 state
            have valuesBound : encodedListSpace values ≤ unit := by
              simp [unit, stepSpaceUnit, values, state]
              omega
            have get0 := getCost_le_budget 0 values unit (by omega) valuesBound
            have get1 := getCost_le_budget 1 values unit (by omega) valuesBound
            have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
            have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
            have get4 := getCost_le_budget 4 values unit (by omega) valuesBound
            have get5 := getCost_le_budget 5 values unit (by omega) valuesBound
            have get6 := getCost_le_budget 6 values unit (by omega) valuesBound
            have drop7 := dropCost_le_budget 7 values unit (by omega) valuesBound
            have identity := idCost_le_budget values unit valuesBound
            have one := oneCost_le_budget values unit valuesBound
            have tail := listCodeTailCost_le_linear (depth :: values)
            have depthBits := listCodeEncodeNat_length_mono
              (show depth ≤ depth + 1 by omega)
            have explicitValuesBound := valuesBound
            have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
            have oneBits : (Computability.encodeNat 1).length = 1 := rfl
            rw [show stepCost tromino periodicStrip 0 state =
                1000000000000000000000000000000 * unit by rfl]
            simp [fieldsCost, branchZeroZeroCost, branchZeroSuccCost,
              branchZeroTestCost, prependCost, values, state, fieldFits,
              getField, oneField, FiniteState.divideEvalProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.divideOptionBoolTag, zeroBits, oneBits]
              at get0 get1 get2 get3 get4 get5 get6 drop7 identity one tail depthBits explicitValuesBound ⊢
            omega
          | succ middle =>
            let state : FiniteState.DivideEvalState :=
              { query := { depth := depth + 1, first := first, last := last },
                stack := stack, answer := none }
            let fieldFits : List (FieldFit values) :=
              [getField 0 values, getField 1 values, succField 2 values,
                zeroField values, predecessorField 4 values,
                getField 5 values, predecessorField 1 values,
                predecessorField 4 values, getField 5 values,
                getField 6 values, predecessorField 1 values,
                zeroField values, zeroField values]
            have countBranch := fields values fieldFits (drop 7 values)
            have depthBranch := branchZero_succ
              (whenZero := FiniteState.DivideEvalPartrec.noneCountZero)
              (testValue := middle + 1)
              (by omega) (get 1 values)
              (by simpa [values, state, fieldFits] using countBranch)
            have answerBranch := branchZero_succ
              (whenZero := FiniteState.DivideEvalPartrec.noneDepthZero
                (stripBaseBoolCode tromino))
              (testValue := depth + 1)
              (by omega) (get 4 values)
              (by simpa [values, state] using depthBranch)
            have whole := branchZero_zero
              (whenSucc := FiniteState.DivideEvalPartrec.answerSome)
              (testValue := 0) rfl
              (get 3 values) answerBranch
            have wholeFits := (by
              simpa [FiniteState.DivideEvalPartrec.stepCode,
              FiniteState.DivideEvalPartrec.answerNone,
              FiniteState.DivideEvalPartrec.noneDepthSucc,
              FiniteState.DivideEvalPartrec.noneCountSucc,
              FiniteState.DivideEvalPartrec.field,
              FiniteState.DivideEvalPartrec.predecessorField,
              FiniteState.DivideEvalPartrec.fields,
              FiniteState.divideEvalProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.DivideFrame.toNatList,
              FiniteState.divideStackToNatList,
              FiniteState.divideEvalStep, values, state, fieldFits,
              getField, succField, zeroField, predecessorField,
              FiniteState.divideBoolTag,
              FiniteState.divideOptionBoolTag] using whole)
            apply wholeFits.mono
            let unit := stepSpaceUnit tromino periodicStrip (middle + 1) state
            have valuesBound : encodedListSpace values ≤ unit := by
              simp [unit, stepSpaceUnit, values, state]
              omega
            have get0 := getCost_le_budget 0 values unit (by omega) valuesBound
            have get1 := getCost_le_budget 1 values unit (by omega) valuesBound
            have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
            have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
            have get4 := getCost_le_budget 4 values unit (by omega) valuesBound
            have get5 := getCost_le_budget 5 values unit (by omega) valuesBound
            have get6 := getCost_le_budget 6 values unit (by omega) valuesBound
            have drop7 := dropCost_le_budget 7 values unit (by omega) valuesBound
            have identity := idCost_le_budget values unit valuesBound
            have zero := zeroCost_le_budget values unit valuesBound
            have successor := successorFieldCost_le_budget 2 values unit
              (by omega) valuesBound
            have predecessor1 := predecessorFieldCost_le_budget 1 values unit
              (by omega) valuesBound
            have predecessor4 := predecessorFieldCost_le_budget 4 values unit
              (by omega) valuesBound
            have middleTail := listCodeTailCost_le_linear (middle :: values)
            have depthTail := listCodeTailCost_le_linear (depth :: values)
            have middleBits := listCodeEncodeNat_length_mono
              (show middle ≤ middle + 1 by omega)
            have depthBits := listCodeEncodeNat_length_mono
              (show depth ≤ depth + 1 by omega)
            have stackBits := encodeNat_succ_length_le stack.length
            have explicitValuesBound := valuesBound
            have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
            have oneBits : (Computability.encodeNat 1).length = 1 := rfl
            rw [show stepCost tromino periodicStrip (middle + 1) state =
                1000000000000000000000000000000 * unit by rfl]
            simp [fieldsCost, branchZeroZeroCost, branchZeroSuccCost,
              branchZeroTestCost, prependCost, values, state, fieldFits,
              getField, succField, zeroField, predecessorField,
              FiniteState.divideEvalProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.DivideFrame.toNatList,
              FiniteState.divideStackToNatList,
              FiniteState.divideOptionBoolTag, FiniteState.divideBoolTag,
              zeroBits, oneBits]
              at get0 get1 get2 get3 get4 get5 get6 drop7 identity zero successor predecessor1 predecessor4 middleTail depthTail middleBits depthBits stackBits explicitValuesBound ⊢
            omega
      | some answerValue =>
        cases stack with
        | nil =>
          let state : FiniteState.DivideEvalState :=
            { query := { depth := depth, first := first, last := last },
              stack := [], answer := some answerValue }
          have answerTest :
              Turing.PartrecToTM2.EvaluatorCodeFits
                (Turing.ToPartrec.Code.get 3) values
                [FiniteState.divideBoolTag answerValue + 1]
                (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 3 values) := by
            cases answerValue <;>
            simpa [values, state, FiniteState.divideEvalProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.divideBoolTag,
              FiniteState.divideOptionBoolTag] using
                Turing.PartrecToTM2.EvaluatorCodeFits.get 3 values
          have stackBranch := branchZero_zero
            (whenSucc := FiniteState.DivideEvalPartrec.someFrame)
            (testValue := 0) rfl
            (get 2 values) (id values)
          have whole := branchZero_succ
            (whenZero := FiniteState.DivideEvalPartrec.answerNone
              (stripBaseBoolCode tromino))
            (testValue := FiniteState.divideBoolTag answerValue + 1)
            (by cases answerValue <;> simp [FiniteState.divideBoolTag])
            answerTest
            (by simpa [values, state] using stackBranch)
          cases answerValue
          all_goals
            have wholeFits := (by
              simpa [FiniteState.DivideEvalPartrec.stepCode,
                FiniteState.DivideEvalPartrec.answerSome,
                FiniteState.DivideEvalPartrec.field,
                FiniteState.divideEvalProgramList,
                FiniteState.DivideEvalState.toNatList,
                FiniteState.divideEvalStep, values, state,
                FiniteState.divideBoolTag,
                FiniteState.divideOptionBoolTag] using whole)
            apply wholeFits.mono
            let unit := stepSpaceUnit tromino periodicStrip stateCount state
            have valuesBound : encodedListSpace values ≤ unit := by
              simp [unit, stepSpaceUnit, values, state]
              omega
            have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
            have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
            have identity := idCost_le_budget values unit valuesBound
            have tail0 := listCodeTailCost_le_linear (0 :: values)
            have tail1 := listCodeTailCost_le_linear (1 :: values)
            have explicitValuesBound := valuesBound
            have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
            have oneBits : (Computability.encodeNat 1).length = 1 := rfl
            have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
            rw [show stepCost tromino periodicStrip stateCount state =
                1000000000000000000000000000000 * unit by rfl]
            simp [branchZeroZeroCost, branchZeroSuccCost,
              branchZeroTestCost, prependCost, values, state,
              FiniteState.divideEvalProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.divideOptionBoolTag, FiniteState.divideBoolTag,
              zeroBits, oneBits, twoBits]
              at get2 get3 identity tail0 tail1 explicitValuesBound ⊢
            omega
        | cons frame rest =>
          cases frame with
          | mk frameDepth frameFirst frameLast middle accumulated leftAnswer =>
            cases leftAnswer with
            | none =>
              let state : FiniteState.DivideEvalState :=
                { query := { depth := depth, first := first, last := last },
                  stack := (⟨frameDepth, frameFirst, frameLast, middle,
                    accumulated, none⟩ : FiniteState.DivideFrame) :: rest,
                  answer := some answerValue }
              let fieldFits : List (FieldFit values) :=
                [getField 0 values, getField 1 values, getField 2 values,
                  zeroField values, getField 7 values, getField 10 values,
                  getField 9 values, getField 7 values, getField 8 values,
                  getField 9 values, getField 10 values, getField 11 values,
                  getField 3 values]
              have answerTest :
                  Turing.PartrecToTM2.EvaluatorCodeFits
                    (Turing.ToPartrec.Code.get 3) values
                    [FiniteState.divideBoolTag answerValue + 1]
                    (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 3 values) := by
                cases answerValue <;>
                simpa [values, state, FiniteState.divideEvalProgramList,
                  FiniteState.DivideEvalState.toNatList,
                  FiniteState.DivideFrame.toNatList,
                  FiniteState.divideStackToNatList,
                  FiniteState.divideBoolTag,
                  FiniteState.divideOptionBoolTag] using
                    Turing.PartrecToTM2.EvaluatorCodeFits.get 3 values
              have leftBranch := fields values fieldFits (drop 13 values)
              have frameBranch := branchZero_zero
                (whenSucc := FiniteState.DivideEvalPartrec.someLeftSome)
                (testValue := 0) rfl
                (get 12 values)
                (by simpa [values, state, fieldFits] using leftBranch)
              have stackBranch := branchZero_succ
                (whenZero := Turing.ToPartrec.Code.id)
                (testValue := rest.length + 1)
                (by omega) (get 2 values)
                (by simpa [values, state] using frameBranch)
              have whole := branchZero_succ
                (whenZero := FiniteState.DivideEvalPartrec.answerNone
                  (stripBaseBoolCode tromino))
                (testValue := FiniteState.divideBoolTag answerValue + 1)
                (by cases answerValue <;> simp [FiniteState.divideBoolTag])
                answerTest
                (by simpa [values, state] using stackBranch)
              cases answerValue <;> cases accumulated
              all_goals
                have wholeFits := (by
                  simpa [FiniteState.DivideEvalPartrec.stepCode,
                    FiniteState.DivideEvalPartrec.answerSome,
                    FiniteState.DivideEvalPartrec.someFrame,
                    FiniteState.DivideEvalPartrec.someLeftNone,
                    FiniteState.DivideEvalPartrec.field,
                    FiniteState.DivideEvalPartrec.fields,
                    FiniteState.divideEvalProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideEvalStep, values, state, fieldFits,
                    getField, zeroField,
                    FiniteState.divideBoolTag,
                    FiniteState.divideOptionBoolTag] using whole)
                apply wholeFits.mono
                let unit := stepSpaceUnit tromino periodicStrip stateCount state
                have valuesBound : encodedListSpace values ≤ unit := by
                  simp [unit, stepSpaceUnit, values, state]
                  omega
                have get0 := getCost_le_budget 0 values unit (by omega) valuesBound
                have get1 := getCost_le_budget 1 values unit (by omega) valuesBound
                have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
                have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
                have get7 := getCost_le_budget 7 values unit (by omega) valuesBound
                have get8 := getCost_le_budget 8 values unit (by omega) valuesBound
                have get9 := getCost_le_budget 9 values unit (by omega) valuesBound
                have get10 := getCost_le_budget 10 values unit (by omega) valuesBound
                have get11 := getCost_le_budget 11 values unit (by omega) valuesBound
                have get12 := getCost_le_budget 12 values unit (by omega) valuesBound
                have drop13 : dropCost 13 values ≤ 140000 * (unit + 1) := by
                  exact (dropCost_le_linear 13 values).trans (by
                    norm_num
                    gcongr)
                have identity := idCost_le_budget values unit valuesBound
                have zero := zeroCost_le_budget values unit valuesBound
                have restTail := listCodeTailCost_le_linear (rest.length :: values)
                have tail0 := listCodeTailCost_le_linear (0 :: values)
                have tail1 := listCodeTailCost_le_linear (1 :: values)
                have restBits := listCodeEncodeNat_length_mono
                  (show rest.length ≤ rest.length + 1 by omega)
                have explicitValuesBound := valuesBound
                have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
                have oneBits : (Computability.encodeNat 1).length = 1 := rfl
                have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
                rw [show stepCost tromino periodicStrip stateCount state =
                    1000000000000000000000000000000 * unit by rfl]
                simp [fieldsCost, branchZeroZeroCost, branchZeroSuccCost,
                  branchZeroTestCost, prependCost, values, state, fieldFits,
                  getField, zeroField, FiniteState.divideEvalProgramList,
                  FiniteState.DivideEvalState.toNatList,
                  FiniteState.DivideFrame.toNatList,
                  FiniteState.divideStackToNatList,
                  FiniteState.divideOptionBoolTag, FiniteState.divideBoolTag,
                  zeroBits, oneBits, twoBits]
                  at get0 get1 get2 get3 get7 get8 get9 get10 get11 get12 drop13 identity zero restTail tail0 tail1 restBits explicitValuesBound ⊢
                omega
            | some leftValue =>
              cases middle with
              | zero =>
                let state : FiniteState.DivideEvalState :=
                  { query := { depth := depth, first := first, last := last },
                    stack := (⟨frameDepth, frameFirst, frameLast, 0,
                      accumulated, some leftValue⟩ :
                        FiniteState.DivideFrame) :: rest,
                    answer := some answerValue }
                let leftFit := predecessorField 12 values
                let answerFit := predecessorField 3 values
                let both := boolAnd leftFit.fits answerFit.fits
                let accumulatedFit := boolOr (get 11 values) both
                let rawAccumulatedField : FieldFit values :=
                  { code := FiniteState.DivideEvalPartrec.accumulatedCode,
                    output := if values[11]?.getD 0 = 0 ∧
                        (¬(values[12]?.getD 0).pred = 0 →
                          (values[3]?.getD 0).pred = 0)
                      then 0 else 1,
                    cost := _,
                    fits := by
                      simpa [FiniteState.DivideEvalPartrec.accumulatedCode,
                        FiniteState.DivideEvalPartrec.predecessorField,
                        FiniteState.DivideEvalPartrec.field, leftFit,
                        answerFit, StripSavitchStep.predecessorField] using
                          accumulatedFit }
                let accumulatedField : FieldFit values :=
                  someBoolField values
                    FiniteState.DivideEvalPartrec.accumulatedCode
                    rawAccumulatedField.output rawAccumulatedField.cost
                    rawAccumulatedField.fits
                let fieldFits : List (FieldFit values) :=
                  [getField 0 values, getField 1 values,
                    predecessorField 2 values, accumulatedField,
                    getField 4 values, getField 5 values, getField 6 values]
                have answerTest :
                    Turing.PartrecToTM2.EvaluatorCodeFits
                      (Turing.ToPartrec.Code.get 3) values
                      [FiniteState.divideBoolTag answerValue + 1]
                      (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 3 values) := by
                  cases answerValue <;>
                  simpa [values, state, FiniteState.divideEvalProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideBoolTag,
                    FiniteState.divideOptionBoolTag] using
                      Turing.PartrecToTM2.EvaluatorCodeFits.get 3 values
                have leftTest :
                    Turing.PartrecToTM2.EvaluatorCodeFits
                      (Turing.ToPartrec.Code.get 12) values
                      [FiniteState.divideBoolTag leftValue + 1]
                      (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 12 values) := by
                  cases leftValue <;>
                  simpa [values, state, FiniteState.divideEvalProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideBoolTag,
                    FiniteState.divideOptionBoolTag] using
                      Turing.PartrecToTM2.EvaluatorCodeFits.get 12 values
                have middleBranch := fields values fieldFits (drop 13 values)
                have leftBranch := branchZero_succ
                  (whenZero := FiniteState.DivideEvalPartrec.someLeftNone)
                  (testValue := FiniteState.divideBoolTag leftValue + 1)
                  (by cases leftValue <;> simp [FiniteState.divideBoolTag])
                  leftTest
                  (by
                    have zeroBranch := branchZero_zero
                      (whenSucc :=
                        FiniteState.DivideEvalPartrec.someLeftSomeMiddleSucc)
                      (testValue := 0) rfl
                      (get 10 values)
                      (by simpa [values, state, fieldFits,
                          accumulatedField] using middleBranch)
                    simpa [FiniteState.DivideEvalPartrec.someLeftSome] using
                      zeroBranch)
                have frameBranch := branchZero_succ
                  (whenZero := Turing.ToPartrec.Code.id)
                  (testValue := rest.length + 1)
                  (by omega) (get 2 values)
                  (by simpa [values, state] using leftBranch)
                have whole := branchZero_succ
                  (whenZero := FiniteState.DivideEvalPartrec.answerNone
                    (stripBaseBoolCode tromino))
                  (testValue := FiniteState.divideBoolTag answerValue + 1)
                  (by cases answerValue <;> simp [FiniteState.divideBoolTag])
                    answerTest
                  (by simpa [values, state] using frameBranch)
                cases answerValue <;> cases leftValue <;> cases accumulated
                all_goals
                  have wholeFits := (by
                    simpa [FiniteState.DivideEvalPartrec.stepCode,
                      FiniteState.DivideEvalPartrec.answerSome,
                      FiniteState.DivideEvalPartrec.someFrame,
                      FiniteState.DivideEvalPartrec.someLeftSome,
                      FiniteState.DivideEvalPartrec.someLeftSomeMiddleZero,
                      FiniteState.DivideEvalPartrec.accumulatedCode,
                      FiniteState.DivideEvalPartrec.field,
                      FiniteState.DivideEvalPartrec.predecessorField,
                      FiniteState.DivideEvalPartrec.fields,
                      FiniteState.divideEvalProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideEvalStep, values, state, fieldFits,
                      accumulatedField, rawAccumulatedField, someBoolField,
                      getField, StripSavitchStep.predecessorField,
                      FiniteState.divideBoolTag,
                      FiniteState.divideOptionBoolTag] using whole)
                  apply wholeFits.mono
                  let unit := stepSpaceUnit tromino periodicStrip stateCount state
                  have valuesBound : encodedListSpace values ≤ unit := by
                    simp [unit, stepSpaceUnit, values, state]
                    omega
                  have get0 := getCost_le_budget 0 values unit (by omega) valuesBound
                  have get1 := getCost_le_budget 1 values unit (by omega) valuesBound
                  have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
                  have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
                  have get4 := getCost_le_budget 4 values unit (by omega) valuesBound
                  have get5 := getCost_le_budget 5 values unit (by omega) valuesBound
                  have get6 := getCost_le_budget 6 values unit (by omega) valuesBound
                  have get10 := getCost_le_budget 10 values unit (by omega) valuesBound
                  have get11 := getCost_le_budget 11 values unit (by omega) valuesBound
                  have get12 := getCost_le_budget 12 values unit (by omega) valuesBound
                  have pred2 := predecessorFieldCost_le_budget 2 values unit
                    (by omega) valuesBound
                  have pred3 := predecessorFieldCost_le_budget 3 values unit
                    (by omega) valuesBound
                  have pred12 := predecessorFieldCost_le_budget 12 values unit
                    (by omega) valuesBound
                  have drop13 : dropCost 13 values ≤ 140000 * (unit + 1) := by
                    exact (dropCost_le_linear 13 values).trans (by
                      norm_num
                      gcongr)
                  have identity := idCost_le_budget values unit valuesBound
                  have leftOutput : (predecessorField 12 values).output ≤ 1 := by
                    simp [predecessorField, values, state,
                      FiniteState.divideEvalProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideOptionBoolTag,
                      FiniteState.divideBoolTag]
                  have answerOutput : (predecessorField 3 values).output ≤ 1 := by
                    simp [predecessorField, values, state,
                      FiniteState.divideEvalProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideOptionBoolTag,
                      FiniteState.divideBoolTag]
                  have accumulatedOutput : values[11]?.getD 0 ≤ 1 := by
                    simp [values, state, FiniteState.divideEvalProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideBoolTag,
                      FiniteState.divideOptionBoolTag]
                  have rawOutputBound : rawAccumulatedField.output ≤ 1 := by
                    dsimp only [rawAccumulatedField]
                    split <;> omega
                  have rawCost : rawAccumulatedField.cost =
                      boolOrCost values (values[11]?.getD 0)
                        (if (predecessorField 12 values).output = 0 ∨
                            (predecessorField 3 values).output = 0
                          then 0 else 1)
                        (getCost 11 values)
                        (boolAndCost values
                          (predecessorField 12 values).output
                          (predecessorField 3 values).output
                          (predecessorField 12 values).cost
                          (predecessorField 3 values).cost) := by
                    rfl
                  have accumulatedFieldBound :
                      accumulatedField.cost ≤
                        accumulatedTagBudget unit := by
                    change someBoolTagCost values rawAccumulatedField.output
                      rawAccumulatedField.cost ≤ _
                    rw [rawCost]
                    exact accumulatedTagCost_le_budget values
                      rawAccumulatedField.output (values[11]?.getD 0)
                      (predecessorField 12 values).output
                      (predecessorField 3 values).output
                      (getCost 11 values)
                      (predecessorField 12 values).cost
                      (predecessorField 3 values).cost unit
                      rawOutputBound accumulatedOutput leftOutput answerOutput
                      valuesBound get11 pred12 pred3
                  have restTail := listCodeTailCost_le_linear (rest.length :: values)
                  have tail0 := listCodeTailCost_le_linear (0 :: values)
                  have tail1 := listCodeTailCost_le_linear (1 :: values)
                  have restBits := listCodeEncodeNat_length_mono
                    (show rest.length ≤ rest.length + 1 by omega)
                  have explicitValuesBound := valuesBound
                  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
                  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
                  have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
                  rw [show stepCost tromino periodicStrip stateCount state =
                      1000000000000000000000000000000 * unit by rfl]
                  simp [fieldsCost, branchZeroZeroCost, branchZeroSuccCost,
                    branchZeroTestCost, prependCost, values, state, fieldFits,
                    accumulatedField, rawAccumulatedField, someBoolField,
                    getField, predecessorField,
                    FiniteState.divideEvalProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideOptionBoolTag, FiniteState.divideBoolTag,
                    zeroBits, oneBits, twoBits]
                    at get0 get1 get2 get3 get4 get5 get6 get10 get11 get12 pred2 pred3 pred12 drop13 identity accumulatedFieldBound restTail tail0 tail1 restBits explicitValuesBound ⊢
                  simp [accumulatedTagBudget, accumulatedRawBudget] at accumulatedFieldBound
                  omega
              | succ previousMiddle =>
                let state : FiniteState.DivideEvalState :=
                  { query := { depth := depth, first := first, last := last },
                    stack := (⟨frameDepth, frameFirst, frameLast,
                      previousMiddle + 1, accumulated, some leftValue⟩ :
                        FiniteState.DivideFrame) :: rest,
                    answer := some answerValue }
                let leftFit := predecessorField 12 values
                let answerFit := predecessorField 3 values
                let both := boolAnd leftFit.fits answerFit.fits
                let accumulatedFit := boolOr (get 11 values) both
                let accumulatedField : FieldFit values :=
                  { code := FiniteState.DivideEvalPartrec.accumulatedCode,
                    output := if values[11]?.getD 0 = 0 ∧
                        (¬(values[12]?.getD 0).pred = 0 →
                          (values[3]?.getD 0).pred = 0)
                      then 0 else 1,
                    cost := _,
                    fits := by
                      simpa [FiniteState.DivideEvalPartrec.accumulatedCode,
                        FiniteState.DivideEvalPartrec.predecessorField,
                        FiniteState.DivideEvalPartrec.field, leftFit,
                        answerFit, StripSavitchStep.predecessorField] using
                          accumulatedFit }
                let fieldFits : List (FieldFit values) :=
                  [getField 0 values, getField 1 values, getField 2 values,
                    zeroField values, getField 7 values, getField 8 values,
                    predecessorField 10 values, getField 7 values,
                    getField 8 values, getField 9 values,
                    predecessorField 10 values, accumulatedField,
                    zeroField values]
                have answerTest :
                    Turing.PartrecToTM2.EvaluatorCodeFits
                      (Turing.ToPartrec.Code.get 3) values
                      [FiniteState.divideBoolTag answerValue + 1]
                      (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 3 values) := by
                  cases answerValue <;>
                  simpa [values, state, FiniteState.divideEvalProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideBoolTag,
                    FiniteState.divideOptionBoolTag] using
                      Turing.PartrecToTM2.EvaluatorCodeFits.get 3 values
                have leftTest :
                    Turing.PartrecToTM2.EvaluatorCodeFits
                      (Turing.ToPartrec.Code.get 12) values
                      [FiniteState.divideBoolTag leftValue + 1]
                      (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 12 values) := by
                  cases leftValue <;>
                  simpa [values, state, FiniteState.divideEvalProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideBoolTag,
                    FiniteState.divideOptionBoolTag] using
                      Turing.PartrecToTM2.EvaluatorCodeFits.get 12 values
                have middleFields := fields values fieldFits (drop 13 values)
                have middleBranch := branchZero_succ
                  (whenZero :=
                    FiniteState.DivideEvalPartrec.someLeftSomeMiddleZero)
                  (testValue := previousMiddle + 1) (by omega)
                  (get 10 values)
                  (by simpa [values, state, fieldFits,
                      accumulatedField] using middleFields)
                have leftBranch := branchZero_succ
                  (whenZero := FiniteState.DivideEvalPartrec.someLeftNone)
                  (testValue := FiniteState.divideBoolTag leftValue + 1)
                  (by cases leftValue <;> simp [FiniteState.divideBoolTag])
                  leftTest
                  (by simpa [FiniteState.DivideEvalPartrec.someLeftSome] using
                    middleBranch)
                have frameBranch := branchZero_succ
                  (whenZero := Turing.ToPartrec.Code.id)
                  (testValue := rest.length + 1)
                  (by omega) (get 2 values)
                  (by simpa [values, state] using leftBranch)
                have whole := branchZero_succ
                  (whenZero := FiniteState.DivideEvalPartrec.answerNone
                    (stripBaseBoolCode tromino))
                  (testValue := FiniteState.divideBoolTag answerValue + 1)
                  (by cases answerValue <;> simp [FiniteState.divideBoolTag])
                  answerTest
                  (by simpa [values, state] using frameBranch)
                cases answerValue <;> cases leftValue <;> cases accumulated
                all_goals
                  have wholeFits := (by
                    simpa [FiniteState.DivideEvalPartrec.stepCode,
                      FiniteState.DivideEvalPartrec.answerSome,
                      FiniteState.DivideEvalPartrec.someFrame,
                      FiniteState.DivideEvalPartrec.someLeftSome,
                      FiniteState.DivideEvalPartrec.someLeftSomeMiddleSucc,
                      FiniteState.DivideEvalPartrec.accumulatedCode,
                      FiniteState.DivideEvalPartrec.field,
                      FiniteState.DivideEvalPartrec.predecessorField,
                      FiniteState.DivideEvalPartrec.fields,
                      FiniteState.divideEvalProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideEvalStep, values, state, fieldFits,
                      accumulatedField, getField, zeroField,
                      StripSavitchStep.predecessorField,
                      FiniteState.divideBoolTag,
                      FiniteState.divideOptionBoolTag] using whole)
                  apply wholeFits.mono
                  let unit := stepSpaceUnit tromino periodicStrip stateCount state
                  have valuesBound : encodedListSpace values ≤ unit := by
                    simp [unit, stepSpaceUnit, values, state]
                    omega
                  have get0 := getCost_le_budget 0 values unit (by omega) valuesBound
                  have get1 := getCost_le_budget 1 values unit (by omega) valuesBound
                  have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
                  have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
                  have get7 := getCost_le_budget 7 values unit (by omega) valuesBound
                  have get8 := getCost_le_budget 8 values unit (by omega) valuesBound
                  have get9 := getCost_le_budget 9 values unit (by omega) valuesBound
                  have get10 := getCost_le_budget 10 values unit (by omega) valuesBound
                  have get11 := getCost_le_budget 11 values unit (by omega) valuesBound
                  have get12 := getCost_le_budget 12 values unit (by omega) valuesBound
                  have pred3 := predecessorFieldCost_le_budget 3 values unit
                    (by omega) valuesBound
                  have pred10 := predecessorFieldCost_le_budget 10 values unit
                    (by omega) valuesBound
                  have pred12 := predecessorFieldCost_le_budget 12 values unit
                    (by omega) valuesBound
                  have drop13 : dropCost 13 values ≤ 140000 * (unit + 1) := by
                    exact (dropCost_le_linear 13 values).trans (by
                      norm_num
                      gcongr)
                  have identity := idCost_le_budget values unit valuesBound
                  have zero := zeroCost_le_budget values unit valuesBound
                  have leftOutput : (predecessorField 12 values).output ≤ 1 := by
                    simp [predecessorField, values, state,
                      FiniteState.divideEvalProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideOptionBoolTag,
                      FiniteState.divideBoolTag]
                  have answerOutput : (predecessorField 3 values).output ≤ 1 := by
                    simp [predecessorField, values, state,
                      FiniteState.divideEvalProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideOptionBoolTag,
                      FiniteState.divideBoolTag]
                  have accumulatedOutput : values[11]?.getD 0 ≤ 1 := by
                    simp [values, state, FiniteState.divideEvalProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideBoolTag,
                      FiniteState.divideOptionBoolTag]
                  have accumulatedFieldOutput : accumulatedField.output ≤ 1 := by
                    dsimp only [accumulatedField]
                    split <;> omega
                  have accumulatedFieldCost : accumulatedField.cost =
                      boolOrCost values (values[11]?.getD 0)
                        (if (predecessorField 12 values).output = 0 ∨
                            (predecessorField 3 values).output = 0
                          then 0 else 1)
                        (getCost 11 values)
                        (boolAndCost values
                          (predecessorField 12 values).output
                          (predecessorField 3 values).output
                          (predecessorField 12 values).cost
                          (predecessorField 3 values).cost) := by
                    rfl
                  have accumulatedFieldBound :
                      accumulatedField.cost ≤ accumulatedRawBudget unit := by
                    rw [accumulatedFieldCost]
                    exact accumulatedRawCost_le_budget values
                      (values[11]?.getD 0)
                      (predecessorField 12 values).output
                      (predecessorField 3 values).output
                      (getCost 11 values)
                      (predecessorField 12 values).cost
                      (predecessorField 3 values).cost unit
                      accumulatedOutput leftOutput answerOutput valuesBound
                      get11 pred12 pred3
                  have middleTail := listCodeTailCost_le_linear
                    (previousMiddle :: values)
                  have restTail := listCodeTailCost_le_linear (rest.length :: values)
                  have tail0 := listCodeTailCost_le_linear (0 :: values)
                  have tail1 := listCodeTailCost_le_linear (1 :: values)
                  have middleBits := listCodeEncodeNat_length_mono
                    (show previousMiddle ≤ previousMiddle + 1 by omega)
                  have restBits := listCodeEncodeNat_length_mono
                    (show rest.length ≤ rest.length + 1 by omega)
                  have explicitValuesBound := valuesBound
                  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
                  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
                  have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
                  rw [show stepCost tromino periodicStrip stateCount state =
                      1000000000000000000000000000000 * unit by rfl]
                  simp [fieldsCost, branchZeroZeroCost, branchZeroSuccCost,
                    branchZeroTestCost, prependCost, values, state, fieldFits,
                    accumulatedField, getField, zeroField, predecessorField,
                    FiniteState.divideEvalProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideOptionBoolTag, FiniteState.divideBoolTag,
                    zeroBits, oneBits, twoBits]
                    at get0 get1 get2 get3 get7 get8 get9 get10 get11 get12 pred3 pred10 pred12 drop13 identity zero accumulatedFieldBound middleTail restTail tail0 tail1 middleBits restBits explicitValuesBound ⊢
                  simp [accumulatedRawBudget] at accumulatedFieldBound
                  omega

end StripSavitchStep

/-- Exact evaluator cost of the two projections feeding the fuel program. -/
def stripReachFuelArgumentsCost (values : List Nat) : Nat :=
  StripSavitchStep.fieldsCost values
    [StripSavitchStep.getField 1 values,
      StripSavitchStep.getField 2 values]
    [] (EvaluatorCodeFits.nilCost values)

theorem stripReachFuelArguments_fits (values : List Nat) :
    EvaluatorCodeFits stripReachFuelArguments values
      [values[1]?.getD 0, values[2]?.getD 0]
      (stripReachFuelArgumentsCost values) := by
  have fit := StripSavitchStep.fields values
    [StripSavitchStep.getField 1 values,
      StripSavitchStep.getField 2 values]
    (EvaluatorCodeFits.nil values)
  simpa [stripReachFuelArguments, stripReachFuelArgumentsCost,
    StripSavitchStep.fieldsCost,
    FiniteState.DivideEvalPartrec.fields,
    FiniteState.DivideEvalPartrec.field,
    StripSavitchStep.getField] using fit

/-- Exact evaluator cost of computing the fuel field from a reachability
request. -/
def stripReachFuelOnInputCost (values : List Nat) : Nat :=
  EvaluatorCodeFits.divideEvalFuelCost
      [values[1]?.getD 0, values[2]?.getD 0] +
    stripReachFuelArgumentsCost values

theorem stripReachFuelOnInput_fits (values : List Nat) :
    EvaluatorCodeFits stripReachFuelOnInput values
      [FiniteState.divideEvalFuel
        (values[1]?.getD 0) (values[2]?.getD 0)]
      (stripReachFuelOnInputCost values) := by
  have fit := EvaluatorCodeFits.comp
    (EvaluatorCodeFits.divideEvalFuel
      [values[1]?.getD 0, values[2]?.getD 0])
    (stripReachFuelArguments_fits values)
  simpa [stripReachFuelOnInput, divideEvalFuelCode,
    stripReachFuelOnInputCost] using fit

private noncomputable def stripReachFuelField (values : List Nat) :
    StripSavitchStep.FieldFit values where
  code := stripReachFuelOnInput
  output := FiniteState.divideEvalFuel
    (values[1]?.getD 0) (values[2]?.getD 0)
  cost := stripReachFuelOnInputCost values
  fits := stripReachFuelOnInput_fits values

private noncomputable def stripReachInputFields (values : List Nat) :
    List (StripSavitchStep.FieldFit values) :=
  [stripReachFuelField values,
    StripSavitchStep.getField 0 values,
    StripSavitchStep.getField 1 values,
    StripSavitchStep.zeroField values,
    StripSavitchStep.zeroField values,
    StripSavitchStep.getField 2 values,
    StripSavitchStep.getField 3 values,
    StripSavitchStep.getField 4 values]

/-- Exact evaluator cost of assembling the countdown and initial flat DFS
state for one indexed reachability query. -/
noncomputable def stripReachInputCost (values : List Nat) : Nat :=
  StripSavitchStep.fieldsCost values (stripReachInputFields values)
    [] (EvaluatorCodeFits.nilCost values)

theorem stripReachInput_fits (values : List Nat) :
    EvaluatorCodeFits stripReachInputCode values
      [FiniteState.divideEvalFuel
          (values[1]?.getD 0) (values[2]?.getD 0),
        values[0]?.getD 0, values[1]?.getD 0, 0, 0,
        values[2]?.getD 0, values[3]?.getD 0, values[4]?.getD 0]
      (stripReachInputCost values) := by
  have fit := StripSavitchStep.fields values
    (stripReachInputFields values) (EvaluatorCodeFits.nil values)
  simpa [stripReachInputCode, stripReachInputCost,
    stripReachInputFields, stripReachFuelField,
    StripSavitchStep.fieldsCost,
    FiniteState.DivideEvalPartrec.fields,
    FiniteState.DivideEvalPartrec.field,
    StripSavitchStep.getField, StripSavitchStep.zeroField] using fit

/-- The five-field request passed to one reachability query fits the common
outer-loop payload envelope. -/
theorem stripReachQueryPayload_encodedListSpace_le
    (periodicStrip : PeriodicStrip) (first last : Nat)
    (firstBelow : first < indexCount periodicStrip)
    (lastBelow : last < indexCount periodicStrip) :
    encodedListSpace
        [Encodable.encode periodicStrip, indexCount periodicStrip,
          stripSearchDepth periodicStrip, first, last] ≤
      stripLoopPayloadSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  have bound := stripCandidatePayload_encodedListSpace_le periodicStrip
    (indexCount periodicStrip) first last false
    (Nat.le_refl _) (Nat.le_of_lt firstBelow) (Nat.le_of_lt lastBelow)
  simp [encodedListSpace_cons, FiniteState.divideBoolTag] at bound ⊢
  omega

private theorem stripReachNilCost_le_linear (values : List Nat) :
    EvaluatorCodeFits.nilCost values ≤
      1000 * (encodedListSpace values + 1) := by
  have headSpace := encodedListSpace_singleton_headI_le values
  have successorBits := encodeNat_succ_length_le values.headI
  simp [EvaluatorCodeFits.nilCost, EvaluatorCodeFits.tailCost,
    EvaluatorCodeFits.succCost, encodedListSpace_cons]
    at headSpace successorBits ⊢
  omega

set_option maxHeartbeats 1000000 in
/-- The complete input adapter, including exact-fuel computation, fits the
reserve assigned to one reachability call. -/
theorem stripReachInputCost_le
    (periodicStrip : PeriodicStrip) (first last : Nat)
    (firstBelow : first < indexCount periodicStrip)
    (lastBelow : last < indexCount periodicStrip) :
    stripReachInputCost
        [Encodable.encode periodicStrip, indexCount periodicStrip,
          stripSearchDepth periodicStrip, first, last] ≤
      1000000 *
        (stripFuelComputationSpaceBound
            ((Complexity.primcodableFinEncoding PeriodicStrip).encode
              periodicStrip).length +
          stripLoopPayloadSpaceBound
            ((Complexity.primcodableFinEncoding PeriodicStrip).encode
              periodicStrip).length +
          stripReachPayloadSpaceBound
            ((Complexity.primcodableFinEncoding PeriodicStrip).encode
              periodicStrip).length + 1) := by
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, last]
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  have inputBound : encodedListSpace values ≤
      stripLoopPayloadSpaceBound inputLength := by
    simpa [values, inputLength] using
      stripReachQueryPayload_encodedListSpace_le
        periodicStrip first last firstBelow lastBelow
  have outputBound := stripReachPayload_encodedListSpace_le
    Tromino.I periodicStrip first last 0 firstBelow lastBelow
  have fuelCost := stripFuelCodeCost_le periodicStrip
  have get0 := EvaluatorCodeFits.listCodeGetCost_le_linear 0 values
  have get1 := EvaluatorCodeFits.listCodeGetCost_le_linear 1 values
  have get2 := EvaluatorCodeFits.listCodeGetCost_le_linear 2 values
  have get3 := EvaluatorCodeFits.listCodeGetCost_le_linear 3 values
  have get4 := EvaluatorCodeFits.listCodeGetCost_le_linear 4 values
  have zero := EvaluatorCodeFits.listCodeZeroCost_le_linear values
  have nil := stripReachNilCost_le_linear values
  simp [stripReachInputCost, stripReachInputFields,
    stripReachFuelField, stripReachFuelOnInputCost,
    stripReachFuelArgumentsCost, StripSavitchStep.fieldsCost,
    EvaluatorCodeFits.prependCost, StripSavitchStep.getField,
    StripSavitchStep.zeroField, values, inputLength,
    FiniteState.divideEvalProgramList,
    FiniteState.divideEvalInitial,
    FiniteState.DivideEvalState.toNatList,
    FiniteState.divideOptionBoolTag,
    FiniteState.divideStackToNatList,
    encodedListSpace_cons, encodedListSpace_nil]
    at inputBound outputBound fuelCost get0 get1 get2 get3 get4 zero nil ⊢
  omega

/-- Every reachable strip-specialized Savitch transition has the common
input-polynomial cost needed by the tail iterator. -/
theorem stripSavitchStepCost_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (stateCount : Nat) (state : FiniteState.DivideEvalState)
    (indices : state.IndicesBelow (indexCount periodicStrip))
    (stateSpace :
      encodedListSpace
          (FiniteState.divideEvalProgramList
            (Encodable.encode periodicStrip) stateCount state) ≤
        stripReachPayloadSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length) :
    StripSavitchStep.stepCost tromino periodicStrip stateCount state ≤
      stripSavitchStepSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  have firstBound := indices.1.1
  have lastBound := indices.1.2
  have adapter := StripSavitchStep.baseArgumentsCost_le_linear
    (Encodable.encode periodicStrip) stateCount state
  have stateSpace' :
      encodedListSpace
          (FiniteState.divideEvalProgramList
            (Encodable.encode periodicStrip) stateCount state) ≤
        stripReachPayloadSpaceBound inputLength := by
    simpa [inputLength] using stateSpace
  have adapterBound :
      StripSavitchStep.baseArgumentsCost
          (Encodable.encode periodicStrip) stateCount state ≤
        10000000 * (stripReachPayloadSpaceBound inputLength + 1) :=
    adapter.trans (by gcongr)
  have leafLocal :=
    Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionCost_le_polynomialSpaceBound
      tromino periodicStrip state.query.first state.query.last
  have leafGlobal := stripBaseTransitionPolynomialSpaceBound_le_leaf
    tromino periodicStrip state.query.first state.query.last
      firstBound lastBound
  have leafCost :
      Turing.PartrecToTM2.EvaluatorCodeFits.stripBaseTransitionCost
          tromino periodicStrip state.query.first state.query.last ≤
        stripTransitionLeafSpaceBound inputLength :=
    leafLocal.trans (by simpa [inputLength] using leafGlobal)
  simp only [StripSavitchStep.stepCost, StripSavitchStep.stepSpaceUnit,
    StripSavitchStep.baseBoolCost]
  change _ ≤ stripSavitchStepSpaceBound inputLength
  simp only [stripSavitchStepSpaceBound]
  omega

open Turing.PartrecToTM2.EvaluatorCodeFits

private theorem stripSavitchBodyCost_le
    (inputLength remaining : Nat) (payload output : List Nat)
    (stepCost : Nat)
    (inputBound :
      encodedListSpace (remaining :: payload) ≤
        stripReachPayloadSpaceBound inputLength)
    (outputBound :
      encodedListSpace output ≤
        stripReachPayloadSpaceBound inputLength)
    (stepBound : stepCost ≤ stripSavitchStepSpaceBound inputLength) :
    flatCountdownBodyCost (fun _ => output) (fun _ => stepCost)
        remaining payload ≤
      stripSavitchBodySpaceBound inputLength := by
  cases remaining with
  | zero =>
      have payloadBound := listCodeEncodedListSpace_tail_le (0 :: payload)
      simp [flatCountdownBodyCost, zeroPrimeCost,
        stripSavitchBodySpaceBound, encodedListSpace_cons] at *
      omega
  | succ remaining =>
      let values := remaining :: payload
      have predecessorBits := listCodeEncodeNat_length_mono
        (show remaining ≤ remaining + 1 by omega)
      have valuesBound :
          encodedListSpace values ≤
            stripReachPayloadSpaceBound inputLength := by
        simp [values, encodedListSpace_cons] at inputBound ⊢
        omega
      have tailBound := listCodeTailCost_le_linear values
      have headBound := headCost_le values
      have zeroBound := listCodeZeroCost_le_linear values
      have successorZero := succCost_le [0]
      have remainingField :
          (Computability.encodeNat remaining).length + 1 ≤
            encodedListSpace values := by
        simp [values, encodedListSpace_cons]
      have outputWithCounter :
          encodedListSpace (remaining :: output) ≤
            2 * (stripReachPayloadSpaceBound inputLength + 1) := by
        simp [encodedListSpace_cons] at outputBound ⊢
        omega
      have oneBits : (Computability.encodeNat 1).length = 1 := rfl
      have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
      simp [flatCountdownBodyCost, flatCountdownSuccBranchCost,
        prependCost, oneCost, values, stripSavitchBodySpaceBound,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] at inputBound outputBound stepBound tailBound headBound zeroBound successorZero outputWithCounter ⊢
      omega

/-- Total list transformer used to state the flat iterator invariant.  On a
machine-facing evaluator payload it is exactly one semantic Savitch step. -/
def stripSavitchProgramStep
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (stateCount : Nat) (values : List Nat) : List Nat :=
  FiniteState.divideEvalProgramList
    (Encodable.encode periodicStrip) stateCount
    (FiniteState.divideEvalStep stateCount
      (indexedTransitionRawBool tromino periodicStrip)
      (FiniteState.DivideEvalState.ofNatList (values.drop 3)))

@[simp]
theorem stripSavitchProgramStep_programList
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (stateCount : Nat) (state : FiniteState.DivideEvalState) :
    stripSavitchProgramStep tromino periodicStrip stateCount
        (FiniteState.divideEvalProgramList
          (Encodable.encode periodicStrip) stateCount state) =
      FiniteState.divideEvalProgramList
        (Encodable.encode periodicStrip) stateCount
        (FiniteState.divideEvalStep stateCount
          (indexedTransitionRawBool tromino periodicStrip) state) := by
  simp [stripSavitchProgramStep,
    FiniteState.divideEvalProgramList]

theorem stripSavitchProgramStep_iterate
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (stateCount steps : Nat) (state : FiniteState.DivideEvalState) :
    ((stripSavitchProgramStep tromino periodicStrip stateCount)^[steps])
        (FiniteState.divideEvalProgramList
          (Encodable.encode periodicStrip) stateCount state) =
      FiniteState.divideEvalProgramList
        (Encodable.encode periodicStrip) stateCount
        (((FiniteState.divideEvalStep stateCount
          (indexedTransitionRawBool tromino periodicStrip))^[steps]) state) := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        induction, stripSavitchProgramStep_programList]

/-- Reachable configurations of one canonical strip reachability countdown. -/
def StripSavitchReachable
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last remaining : Nat) (values : List Nat) : Prop :=
  ∃ taken,
    remaining + taken =
      FiniteState.divideEvalFuel
        (indexCount periodicStrip) (stripSearchDepth periodicStrip) ∧
    values =
      FiniteState.divideEvalProgramList
        (Encodable.encode periodicStrip) (indexCount periodicStrip)
        (((FiniteState.divideEvalStep (indexCount periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip))^[taken])
            (FiniteState.divideEvalInitial
              (stripSearchDepth periodicStrip) first last))

theorem stripSavitchReachable_initial
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    StripSavitchReachable tromino periodicStrip first last
      (FiniteState.divideEvalFuel
        (indexCount periodicStrip) (stripSearchDepth periodicStrip))
      (FiniteState.divideEvalProgramList
        (Encodable.encode periodicStrip) (indexCount periodicStrip)
        (FiniteState.divideEvalInitial
          (stripSearchDepth periodicStrip) first last)) := by
  exact ⟨0, by omega, rfl⟩

theorem stripSavitchReachable_step
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last remaining : Nat) (values : List Nat)
    (reachable :
      StripSavitchReachable tromino periodicStrip first last
        (remaining + 1) values) :
    StripSavitchReachable tromino periodicStrip first last remaining
      (stripSavitchProgramStep tromino periodicStrip
        (indexCount periodicStrip) values) := by
  obtain ⟨taken, total, rfl⟩ := reachable
  refine ⟨taken + 1, by omega, ?_⟩
  rw [stripSavitchProgramStep_programList,
    Function.iterate_succ_apply']

set_option maxHeartbeats 1000000 in
/-- The entire exact-fuel Savitch countdown reuses the same polynomial body
reserve at every tail-recursive iteration. -/
theorem stripSavitchFlatUniform
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat)
    (firstBelow : first < indexCount periodicStrip)
    (lastBelow : last < indexCount periodicStrip) :
    Turing.PartrecToTM2.EvaluatorCodeFits
      (Turing.ToPartrec.Code.flatIterate
        (FiniteState.DivideEvalPartrec.stepCode
          (stripBaseBoolCode tromino)))
      (FiniteState.divideEvalFuel
          (indexCount periodicStrip) (stripSearchDepth periodicStrip) ::
        FiniteState.divideEvalProgramList
          (Encodable.encode periodicStrip) (indexCount periodicStrip)
          (FiniteState.divideEvalInitial
            (stripSearchDepth periodicStrip) first last))
      (FiniteState.divideEvalProgramList
        (Encodable.encode periodicStrip) (indexCount periodicStrip)
        (((FiniteState.divideEvalStep (indexCount periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip))^[
            FiniteState.divideEvalFuel
              (indexCount periodicStrip) (stripSearchDepth periodicStrip)])
          (FiniteState.divideEvalInitial
            (stripSearchDepth periodicStrip) first last)))
      (stripSavitchBodySpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length) where
  input_space := by
    have input := stripReachCountdownPayload_encodedListSpace_le
      tromino periodicStrip first last 0
      (FiniteState.divideEvalFuel
        (indexCount periodicStrip) (stripSearchDepth periodicStrip))
      firstBelow lastBelow (Nat.le_refl _)
    exact input.trans (by
      simp [stripSavitchBodySpaceBound, stripSavitchStepSpaceBound]
      omega)
  output_space := by
    have output := stripReachStatePayload_encodedListSpace_le
      tromino periodicStrip first last
      (FiniteState.divideEvalFuel
        (indexCount periodicStrip) (stripSearchDepth periodicStrip))
      firstBelow lastBelow
    exact output.trans (by
      simp [stripSavitchBodySpaceBound, stripSavitchStepSpaceBound]
      omega)
  call continuation bound budget after := by
    let inputLength :=
      ((Complexity.primcodableFinEncoding PeriodicStrip).encode
        periodicStrip).length
    apply Turing.PartrecToTM2.EvaluatorCallFits.flatIterate_of_reachable_code_fits
      (step := stripSavitchProgramStep tromino periodicStrip
        (indexCount periodicStrip))
      (bodyCost := fun _ _ => stripSavitchBodySpaceBound inputLength)
      (invariant := StripSavitchReachable tromino periodicStrip first last)
    · intro remaining values reachable
      obtain ⟨taken, total, rfl⟩ := reachable
      let state :=
        ((FiniteState.divideEvalStep (indexCount periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip))^[taken])
            (FiniteState.divideEvalInitial
              (stripSearchDepth periodicStrip) first last)
      have indices : state.IndicesBelow (indexCount periodicStrip) := by
        dsimp only [state]
        exact FiniteState.divideEvalIterate_initial_indicesBelow
          (indexCount periodicStrip) (stripSearchDepth periodicStrip)
          first last taken
          (indexedTransitionRawBool tromino periodicStrip)
          firstBelow lastBelow
      have stateSpace :
          encodedListSpace
              (FiniteState.divideEvalProgramList
                (Encodable.encode periodicStrip) (indexCount periodicStrip)
                state) ≤
            stripReachPayloadSpaceBound inputLength := by
        simpa [state, inputLength] using
          stripReachStatePayload_encodedListSpace_le
            tromino periodicStrip first last taken firstBelow lastBelow
      have stepFit := StripSavitchStep.exactStep tromino periodicStrip
        wellFormed (indexCount periodicStrip) state
      have stepBound := stripSavitchStepCost_le tromino periodicStrip
        (indexCount periodicStrip) state indices stateSpace
      have body := flatCountdownBody_of_fit stepFit remaining
      have body' :
          Turing.PartrecToTM2.EvaluatorCodeFits
            (Turing.ToPartrec.Code.flatCountdownBody
              (FiniteState.DivideEvalPartrec.stepCode
                (stripBaseBoolCode tromino)))
            (remaining ::
              FiniteState.divideEvalProgramList
                (Encodable.encode periodicStrip) (indexCount periodicStrip)
                state)
            (Turing.PartrecToTM2.flatCountdownOutput
              (stripSavitchProgramStep tromino periodicStrip
                (indexCount periodicStrip)) remaining
              (FiniteState.divideEvalProgramList
                (Encodable.encode periodicStrip) (indexCount periodicStrip)
                state))
            (flatCountdownBodyCost
              (fun _ =>
                FiniteState.divideEvalProgramList
                  (Encodable.encode periodicStrip) (indexCount periodicStrip)
                  (FiniteState.divideEvalStep (indexCount periodicStrip)
                    (indexedTransitionRawBool tromino periodicStrip) state))
              (fun _ => StripSavitchStep.stepCost tromino periodicStrip
                (indexCount periodicStrip) state)
              remaining
              (FiniteState.divideEvalProgramList
                (Encodable.encode periodicStrip) (indexCount periodicStrip)
                state)) := by
        cases remaining with
        | zero =>
            simpa [Turing.PartrecToTM2.flatCountdownOutput] using body
        | succ remaining =>
            simp only [Turing.PartrecToTM2.flatCountdownOutput]
            rw [stripSavitchProgramStep_programList]
            simpa [Turing.PartrecToTM2.flatCountdownOutput] using body
      apply body'.mono
      have remainingBound :
          remaining ≤ FiniteState.divideEvalFuel
            (indexCount periodicStrip) (stripSearchDepth periodicStrip) := by
        omega
      have inputBound := stripReachCountdownPayload_encodedListSpace_le
        tromino periodicStrip first last taken remaining
        firstBelow lastBelow remainingBound
      have outputBound := stripReachStatePayload_encodedListSpace_le
        tromino periodicStrip first last (taken + 1)
        firstBelow lastBelow
      exact stripSavitchBodyCost_le inputLength remaining
        (FiniteState.divideEvalProgramList
          (Encodable.encode periodicStrip) (indexCount periodicStrip) state)
        (FiniteState.divideEvalProgramList
          (Encodable.encode periodicStrip) (indexCount periodicStrip)
          (FiniteState.divideEvalStep (indexCount periodicStrip)
            (indexedTransitionRawBool tromino periodicStrip) state))
        (StripSavitchStep.stepCost tromino periodicStrip
          (indexCount periodicStrip) state)
        (by simpa [state, inputLength] using inputBound)
        (by
          simpa [state, inputLength, Function.iterate_succ_apply'] using
            outputBound)
        (by simpa [inputLength] using stepBound)
    · exact stripSavitchReachable_initial
        tromino periodicStrip first last
    · exact stripSavitchReachable_step
        tromino periodicStrip first last
    · intro remaining values reachable
      simpa [inputLength] using budget
    · rw [stripSavitchProgramStep_iterate]
      exact after

/-- Final semantic DFS state reached by one canonical exact-fuel strip
reachability query. -/
def stripReachFinalState
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : FiniteState.DivideEvalState :=
  ((FiniteState.divideEvalStep (indexCount periodicStrip)
      (indexedTransitionRawBool tromino periodicStrip))^[
        FiniteState.divideEvalFuel
          (indexCount periodicStrip) (stripSearchDepth periodicStrip)])
    (FiniteState.divideEvalInitial
      (stripSearchDepth periodicStrip) first last)

/-- Exact compositional evaluator cost of a complete indexed reachability
wrapper, from its five input fields through normalized Boolean output. -/
noncomputable def stripReachBoolCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, last]
  let output := FiniteState.divideEvalProgramList
    (Encodable.encode periodicStrip) (indexCount periodicStrip)
    (stripReachFinalState tromino periodicStrip first last)
  EvaluatorCodeFits.predCost
      [FiniteState.divideOptionBoolTag
        (stripReachFinalState tromino periodicStrip first last).answer] +
    (EvaluatorCodeFits.getCost 3 output +
      (stripSavitchBodySpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length +
        stripReachInputCost values))

/-- The complete compiled reachability wrapper has an exact evaluator-space
certificate, including fuel construction, Savitch search, answer projection,
and option-tag normalization. -/
theorem stripReachBool_fits
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat)
    (firstBelow : first < indexCount periodicStrip)
    (lastBelow : last < indexCount periodicStrip) :
    EvaluatorCodeFits (stripReachBoolCode tromino)
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, last]
      [FiniteState.divideBoolTag
        (FiniteState.divideReachIndexDFSBool
          (indexCount periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip)
          (stripSearchDepth periodicStrip) first last)]
      (stripReachBoolCost tromino periodicStrip first last) := by
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, last]
  let finalState := stripReachFinalState tromino periodicStrip first last
  let output := FiniteState.divideEvalProgramList
    (Encodable.encode periodicStrip) (indexCount periodicStrip) finalState
  have inputFit :
      EvaluatorCodeFits stripReachInputCode values
        (FiniteState.divideEvalFuel
            (indexCount periodicStrip) (stripSearchDepth periodicStrip) ::
          FiniteState.divideEvalProgramList
            (Encodable.encode periodicStrip) (indexCount periodicStrip)
            (FiniteState.divideEvalInitial
              (stripSearchDepth periodicStrip) first last))
        (stripReachInputCost values) := by
    simpa [values, FiniteState.divideEvalProgramList,
      FiniteState.divideEvalInitial,
      FiniteState.DivideEvalState.toNatList,
      FiniteState.divideOptionBoolTag,
      FiniteState.divideStackToNatList] using
      stripReachInput_fits values
  have loopFit := stripSavitchFlatUniform tromino periodicStrip wellFormed
    first last firstBelow lastBelow
  have loopWithInput := EvaluatorCodeFits.comp loopFit inputFit
  have loopWithInput' :
      EvaluatorCodeFits
        ((Turing.ToPartrec.Code.flatIterate
          (FiniteState.DivideEvalPartrec.stepCode
            (stripBaseBoolCode tromino))).comp stripReachInputCode)
        values output
        (stripSavitchBodySpaceBound
            ((Complexity.primcodableFinEncoding PeriodicStrip).encode
              periodicStrip).length + stripReachInputCost values) := by
    simpa [finalState, stripReachFinalState, output] using loopWithInput
  have projected := EvaluatorCodeFits.comp
    (EvaluatorCodeFits.get 3 output) loopWithInput'
  have normalized := EvaluatorCodeFits.comp
    (EvaluatorCodeFits.pred_named
      [FiniteState.divideOptionBoolTag finalState.answer]) projected
  have answerTag :
      (FiniteState.divideOptionBoolTag finalState.answer).pred =
        FiniteState.divideBoolTag (finalState.answer.getD false) := by
    cases finalState.answer with
    | none => rfl
    | some answerValue => cases answerValue <;> rfl
  have outputEq :
      [FiniteState.divideOptionBoolTag finalState.answer - 1] =
        [FiniteState.divideBoolTag
          (FiniteState.divideReachIndexDFSBool
            (indexCount periodicStrip)
            (indexedTransitionRawBool tromino periodicStrip)
            (stripSearchDepth periodicStrip) first last)] := by
    rw [Nat.sub_one, answerTag]
    rfl
  have outputEq' :
      Turing.ToPartrec.Code.subtractStepList
          [FiniteState.divideOptionBoolTag finalState.answer] =
        [FiniteState.divideBoolTag
          (FiniteState.divideReachIndexDFSBool
            (indexCount periodicStrip)
            (indexedTransitionRawBool tromino periodicStrip)
            (stripSearchDepth periodicStrip) first last)] := by
    simpa [Turing.ToPartrec.Code.subtractStepList] using outputEq
  rw [outputEq'] at normalized
  simpa [stripReachBoolCode, stripReachBoolCost, values, output,
    finalState, stripReachFinalState, EvaluatorCodeFits.predCost,
    Turing.ToPartrec.Code.subtractStepList] using normalized

/-- Every bounded canonical reachability call fits the one-query polynomial
reserve, independently of its exponential iteration count. -/
theorem stripReachBoolCost_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat)
    (firstBelow : first < indexCount periodicStrip)
    (lastBelow : last < indexCount periodicStrip) :
    stripReachBoolCost tromino periodicStrip first last ≤
      stripReachCallSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, last]
  let finalState := stripReachFinalState tromino periodicStrip first last
  let output := FiniteState.divideEvalProgramList
    (Encodable.encode periodicStrip) (indexCount periodicStrip) finalState
  have inputCost : stripReachInputCost values ≤
      1000000 *
        (stripFuelComputationSpaceBound inputLength +
          stripLoopPayloadSpaceBound inputLength +
          stripReachPayloadSpaceBound inputLength + 1) := by
    simpa [values, inputLength] using
      stripReachInputCost_le periodicStrip first last firstBelow lastBelow
  have outputBound : encodedListSpace output ≤
      stripReachPayloadSpaceBound inputLength := by
    simpa [output, finalState, stripReachFinalState, inputLength] using
      stripReachStatePayload_encodedListSpace_le tromino periodicStrip
        first last
        (FiniteState.divideEvalFuel
          (indexCount periodicStrip) (stripSearchDepth periodicStrip))
        firstBelow lastBelow
  have projected := EvaluatorCodeFits.listCodeGetCost_le_linear 3 output
  have normalized :
      EvaluatorCodeFits.predCost
          [FiniteState.divideOptionBoolTag finalState.answer] ≤ 1000000 := by
    cases answer : finalState.answer with
    | none => native_decide
    | some answerValue => cases answerValue <;> native_decide
  simp [stripReachBoolCost, values, output, finalState, inputLength,
    stripReachCallSpaceBound, stripSavitchBodySpaceBound,
    stripSavitchStepSpaceBound]
    at inputCost outputBound projected normalized ⊢
  omega

/-- Polynomial-cost form of `stripReachBool_fits`, ready to be nested inside
the endpoint cycle-search loops. -/
theorem stripReachBool_fits_polynomial
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat)
    (firstBelow : first < indexCount periodicStrip)
    (lastBelow : last < indexCount periodicStrip) :
    EvaluatorCodeFits (stripReachBoolCode tromino)
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, last]
      [FiniteState.divideBoolTag
        (FiniteState.divideReachIndexDFSBool
          (indexCount periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip)
          (stripSearchDepth periodicStrip) first last)]
      (stripReachCallSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length) :=
  (stripReachBool_fits tromino periodicStrip wellFormed
    first last firstBelow lastBelow).mono
      (stripReachBoolCost_le tromino periodicStrip
        first last firstBelow lastBelow)

namespace StripCandidateStep

/-- Exact evaluator cost of the three-field adapter feeding the raw edge
test in one second-endpoint update. -/
def edgeArgumentsCost (values : List Nat) : Nat :=
  StripSavitchStep.fieldsCost values
    [StripSavitchStep.getField 0 values,
      StripSavitchStep.getField 3 values,
      StripSavitchStep.predecessorField 4 values]
    [] (EvaluatorCodeFits.nilCost values)

theorem edgeArguments (values : List Nat) :
    EvaluatorCodeFits candidateEdgeArguments values
      [values[0]?.getD 0, values[3]?.getD 0,
        (values[4]?.getD 0).pred]
      (edgeArgumentsCost values) := by
  have fit := StripSavitchStep.fields values
    [StripSavitchStep.getField 0 values,
      StripSavitchStep.getField 3 values,
      StripSavitchStep.predecessorField 4 values]
    (EvaluatorCodeFits.nil values)
  simpa [candidateEdgeArguments, candidateSecond,
    edgeArgumentsCost, StripSavitchStep.fieldsCost,
    FiniteState.DivideEvalPartrec.fields,
    FiniteState.DivideEvalPartrec.field,
    FiniteState.DivideEvalPartrec.predecessorField,
    StripSavitchStep.getField,
    StripSavitchStep.predecessorField] using fit

/-- Exact evaluator cost of the five-field adapter feeding reverse
reachability in one second-endpoint update. -/
def reachArgumentsCost (values : List Nat) : Nat :=
  StripSavitchStep.fieldsCost values
    [StripSavitchStep.getField 0 values,
      StripSavitchStep.getField 1 values,
      StripSavitchStep.getField 2 values,
      StripSavitchStep.predecessorField 4 values,
      StripSavitchStep.getField 3 values]
    [] (EvaluatorCodeFits.nilCost values)

theorem reachArguments (values : List Nat) :
    EvaluatorCodeFits candidateReachArguments values
      [values[0]?.getD 0, values[1]?.getD 0,
        values[2]?.getD 0, (values[4]?.getD 0).pred,
        values[3]?.getD 0]
      (reachArgumentsCost values) := by
  have fit := StripSavitchStep.fields values
    [StripSavitchStep.getField 0 values,
      StripSavitchStep.getField 1 values,
      StripSavitchStep.getField 2 values,
      StripSavitchStep.predecessorField 4 values,
      StripSavitchStep.getField 3 values]
    (EvaluatorCodeFits.nil values)
  simpa [candidateReachArguments, candidateSecond,
    reachArgumentsCost, StripSavitchStep.fieldsCost,
    FiniteState.DivideEvalPartrec.fields,
    FiniteState.DivideEvalPartrec.field,
    FiniteState.DivideEvalPartrec.predecessorField,
    StripSavitchStep.getField,
    StripSavitchStep.predecessorField] using fit

private theorem singletonGetDSpace_le
    (index : Nat) (values : List Nat) :
    encodedListSpace [values[index]?.getD 0] ≤
      encodedListSpace values + 1 := by
  induction index generalizing values with
  | zero =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [List.getElem?_cons_zero, Option.getD_some]
          exact encodedListSpace_singleton_headI_le (value :: values)
  | succ index induction =>
      cases values with
      | nil => rfl
      | cons value values =>
          have tail := induction values
          simp only [List.getElem?_cons_succ] at tail ⊢
          exact tail.trans (Nat.add_le_add_right
            (listCodeEncodedListSpace_tail_le (value :: values)) 1)

private theorem predecessorSingletonSpace_le (value : Nat) :
    encodedListSpace [value.pred] ≤ encodedListSpace [value] := by
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  exact Nat.add_le_add_right
    (listCodeEncodeNat_length_mono (Nat.pred_le value)) 1

private theorem nilCost_le_linear (values : List Nat) :
    EvaluatorCodeFits.nilCost values ≤
      1000 * (encodedListSpace values + 1) := by
  have headSpace := encodedListSpace_singleton_headI_le values
  have successorBits := encodeNat_succ_length_le values.headI
  simp [EvaluatorCodeFits.nilCost, EvaluatorCodeFits.tailCost,
    EvaluatorCodeFits.succCost, encodedListSpace_cons]
    at headSpace successorBits ⊢
  omega

private theorem candidateScaledFieldSpace_le (value : Nat) :
    encodedListSpace [2 * value + 4] ≤
      10 * (encodedListSpace [value] + 1) := by
  have product := encodeNat_mul_length_le_sum 2 value
  have sum := encodeNat_add_length_le_sum (2 * value) 4
  have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
  have fourBits : (Computability.encodeNat 4).length = 3 := by native_decide
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  rw [twoBits] at product
  rw [fourBits] at sum
  omega

private theorem predecessorFieldCost_le_linear
    (index : Nat) (values : List Nat) (indexBound : index ≤ 12) :
    (StripSavitchStep.predecessorField index values).cost ≤
      30000000 * (encodedListSpace values + 1) := by
  let value := values[index]?.getD 0
  have projected := singletonGetDSpace_le index values
  have scaled := candidateScaledFieldSpace_le value
  have predecessor := EvaluatorCodeFits.predCost_singleton_le_linear value
  have projection := EvaluatorCodeFits.listCodeGetCost_le_linear index values
  have projectionBound : EvaluatorCodeFits.getCost index values ≤
      130000 * (encodedListSpace values + 1) :=
    projection.trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 10000 (Nat.add_le_add_right indexBound 1)))
  dsimp only [value] at projected scaled predecessor ⊢
  simp only [StripSavitchStep.predecessorField]
  omega

/-- The edge-test adapter is linear in its six-field candidate payload. -/
theorem edgeArgumentsCost_le_linear (values : List Nat) :
    edgeArgumentsCost values ≤
      100000000 * (encodedListSpace values + 1) := by
  have get0 := EvaluatorCodeFits.listCodeGetCost_le_linear 0 values
  have get3 := EvaluatorCodeFits.listCodeGetCost_le_linear 3 values
  have pred4 := predecessorFieldCost_le_linear 4 values (by omega)
  have nil := nilCost_le_linear values
  have field0 := singletonGetDSpace_le 0 values
  have field3 := singletonGetDSpace_le 3 values
  have field4 := singletonGetDSpace_le 4 values
  have pred4Space := predecessorSingletonSpace_le (values[4]?.getD 0)
  simp [edgeArgumentsCost, StripSavitchStep.fieldsCost,
    EvaluatorCodeFits.prependCost, StripSavitchStep.getField,
    StripSavitchStep.predecessorField] at get0 get3 pred4 nil field0 field3 field4 pred4Space ⊢
  omega

/-- The reachability adapter is linear in its six-field candidate payload. -/
theorem reachArgumentsCost_le_linear (values : List Nat) :
    reachArgumentsCost values ≤
      100000000 * (encodedListSpace values + 1) := by
  have get0 := EvaluatorCodeFits.listCodeGetCost_le_linear 0 values
  have get1 := EvaluatorCodeFits.listCodeGetCost_le_linear 1 values
  have get2 := EvaluatorCodeFits.listCodeGetCost_le_linear 2 values
  have get3 := EvaluatorCodeFits.listCodeGetCost_le_linear 3 values
  have pred4 := predecessorFieldCost_le_linear 4 values (by omega)
  have nil := nilCost_le_linear values
  have field0 := singletonGetDSpace_le 0 values
  have field1 := singletonGetDSpace_le 1 values
  have field2 := singletonGetDSpace_le 2 values
  have field3 := singletonGetDSpace_le 3 values
  have field4 := singletonGetDSpace_le 4 values
  have pred4Space := predecessorSingletonSpace_le (values[4]?.getD 0)
  simp [reachArgumentsCost, StripSavitchStep.fieldsCost,
    EvaluatorCodeFits.prependCost, StripSavitchStep.getField,
    StripSavitchStep.predecessorField] at get0 get1 get2 get3 pred4 nil field0 field1 field2 field3 field4 pred4Space ⊢
  omega

def edgeCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (values : List Nat) : Nat :=
  EvaluatorCodeFits.stripTransitionCost tromino periodicStrip
      first secondRemaining.pred + edgeArgumentsCost values

theorem edge
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool) :
    let values :=
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining,
        FiniteState.divideBoolTag found]
    EvaluatorCodeFits (candidateEdgeCode tromino) values
      [FiniteState.divideBoolTag
        (indexedTransitionRawBool tromino periodicStrip
          first secondRemaining.pred)]
      (edgeCost tromino periodicStrip first secondRemaining values) := by
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining,
      FiniteState.divideBoolTag found]
  have leaf := EvaluatorCodeFits.stripTransition
    tromino periodicStrip wellFormed first secondRemaining.pred
  have adapted := edgeArguments values
  have fit := EvaluatorCodeFits.comp leaf adapted
  have outputEq :
      [(indexedTransitionRawBool tromino periodicStrip
        first secondRemaining.pred).toNat] =
      [FiniteState.divideBoolTag
        (indexedTransitionRawBool tromino periodicStrip
          first secondRemaining.pred)] := by
    cases indexedTransitionRawBool tromino periodicStrip
      first secondRemaining.pred <;> rfl
  rw [outputEq] at fit
  simpa [candidateEdgeCode, stripEdgeVectorCode,
    edgeCost, values] using fit

def reachCost
    (periodicStrip : PeriodicStrip) (values : List Nat) : Nat :=
  stripReachCallSpaceBound
      ((Complexity.primcodableFinEncoding PeriodicStrip).encode
        periodicStrip).length +
    reachArgumentsCost values

theorem reach
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) :
    EvaluatorCodeFits (candidateReachCode tromino)
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining,
        FiniteState.divideBoolTag found]
      [FiniteState.divideBoolTag
        (FiniteState.divideReachIndexDFSBool
          (indexCount periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip)
          (stripSearchDepth periodicStrip) secondRemaining.pred first)]
      (reachCost periodicStrip
        [Encodable.encode periodicStrip, indexCount periodicStrip,
          stripSearchDepth periodicStrip, first, secondRemaining,
          FiniteState.divideBoolTag found]) := by
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining,
      FiniteState.divideBoolTag found]
  have endpointBelow : secondRemaining.pred < indexCount periodicStrip := by
    exact (Nat.pred_lt (Nat.ne_of_gt secondPositive)).trans_le secondBound
  have query := stripReachBool_fits_polynomial tromino periodicStrip
    wellFormed secondRemaining.pred first endpointBelow firstBelow
  have adapted := reachArguments values
  have fit := EvaluatorCodeFits.comp query adapted
  simpa [candidateReachCode, reachCost, values] using fit

private def candidateBaseUnit (inputLength : Nat) : Nat :=
  stripReachCallSpaceBound inputLength +
    stripTransitionLeafSpaceBound inputLength +
    stripLoopPayloadSpaceBound inputLength + 1

private theorem candidateValuesSpace_le
    (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) :
    encodedListSpace
        [Encodable.encode periodicStrip, indexCount periodicStrip,
          stripSearchDepth periodicStrip, first, secondRemaining,
          FiniteState.divideBoolTag found] ≤
      stripLoopPayloadSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining,
      FiniteState.divideBoolTag found]
  have payload := stripCandidatePayload_encodedListSpace_le periodicStrip
    0 first secondRemaining found (Nat.zero_le _)
    (Nat.le_of_lt firstBelow) secondBound
  have tail := listCodeEncodedListSpace_tail_le (0 :: values)
  exact tail.trans (by simpa [values] using payload)

theorem edgeCost_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) :
    let inputLength :=
      ((Complexity.primcodableFinEncoding PeriodicStrip).encode
        periodicStrip).length
    let values :=
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining,
        FiniteState.divideBoolTag found]
    edgeCost tromino periodicStrip first secondRemaining values ≤
      100000000 * candidateBaseUnit inputLength := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining,
      FiniteState.divideBoolTag found]
  have endpointBelow : secondRemaining.pred < indexCount periodicStrip :=
    (Nat.pred_lt (Nat.ne_of_gt secondPositive)).trans_le secondBound
  have valuesBound : encodedListSpace values ≤
      stripLoopPayloadSpaceBound inputLength := by
    simpa [values, inputLength] using candidateValuesSpace_le periodicStrip
      first secondRemaining found firstBelow secondBound
  have adapter := edgeArgumentsCost_le_linear values
  have leafPolynomial :=
    EvaluatorCodeFits.stripTransitionCost_le_polynomialSpaceBound
      tromino periodicStrip first secondRemaining.pred
  have leafReserve := stripTransitionPolynomialSpaceBound_le_leaf
    tromino periodicStrip first secondRemaining.pred firstBelow endpointBelow
  have leaf := leafPolynomial.trans leafReserve
  have adapter' : edgeArgumentsCost values ≤
      100000000 * (stripLoopPayloadSpaceBound inputLength + 1) :=
    adapter.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right valuesBound 1))
  calc
    edgeCost tromino periodicStrip first secondRemaining values =
        EvaluatorCodeFits.stripTransitionCost tromino periodicStrip
          first secondRemaining.pred + edgeArgumentsCost values := rfl
    _ ≤ stripTransitionLeafSpaceBound inputLength +
          100000000 * (stripLoopPayloadSpaceBound inputLength + 1) :=
      Nat.add_le_add (by simpa [inputLength] using leaf) adapter'
    _ ≤ 100000000 * candidateBaseUnit inputLength := by
      simp [candidateBaseUnit]
      omega

theorem reachCost_le
    (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) :
    let inputLength :=
      ((Complexity.primcodableFinEncoding PeriodicStrip).encode
        periodicStrip).length
    let values :=
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining,
        FiniteState.divideBoolTag found]
    reachCost periodicStrip values ≤
      100000000 * candidateBaseUnit inputLength := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining,
      FiniteState.divideBoolTag found]
  have valuesBound : encodedListSpace values ≤
      stripLoopPayloadSpaceBound inputLength := by
    simpa [values, inputLength] using candidateValuesSpace_le periodicStrip
      first secondRemaining found firstBelow secondBound
  have adapter := reachArgumentsCost_le_linear values
  have adapter' : reachArgumentsCost values ≤
      100000000 * (stripLoopPayloadSpaceBound inputLength + 1) :=
    adapter.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right valuesBound 1))
  calc
    reachCost periodicStrip values =
        stripReachCallSpaceBound inputLength + reachArgumentsCost values := by
      simp [reachCost, inputLength]
    _ ≤ stripReachCallSpaceBound inputLength +
          100000000 * (stripLoopPayloadSpaceBound inputLength + 1) :=
      Nat.add_le_add_left adapter' _
    _ ≤ 100000000 * candidateBaseUnit inputLength := by
      simp [candidateBaseUnit]
      omega

def foundCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool)
    (values : List Nat) : Nat :=
  let edge := indexedTransitionRawBool tromino periodicStrip
    first secondRemaining.pred
  let reachable := FiniteState.divideReachIndexDFSBool
    (indexCount periodicStrip)
    (indexedTransitionRawBool tromino periodicStrip)
    (stripSearchDepth periodicStrip) secondRemaining.pred first
  let bothCost := EvaluatorCodeFits.boolAndCost values
    (FiniteState.divideBoolTag edge)
    (FiniteState.divideBoolTag reachable)
    (edgeCost tromino periodicStrip first secondRemaining values)
    (reachCost periodicStrip values)
  EvaluatorCodeFits.boolOrCost values
    (FiniteState.divideBoolTag found)
    (FiniteState.divideBoolTag (edge && reachable))
    (EvaluatorCodeFits.getCost 5 values) bothCost

theorem found
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) :
    let values :=
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining,
        FiniteState.divideBoolTag found]
    EvaluatorCodeFits (candidateFoundCode tromino) values
      [FiniteState.divideBoolTag
        (found || cycleCandidateBool tromino periodicStrip
          (indexCount periodicStrip) (stripSearchDepth periodicStrip)
          first secondRemaining.pred)]
      (foundCost tromino periodicStrip first secondRemaining found values) := by
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining,
      FiniteState.divideBoolTag found]
  let edgeValue := indexedTransitionRawBool tromino periodicStrip
    first secondRemaining.pred
  let reachValue := FiniteState.divideReachIndexDFSBool
    (indexCount periodicStrip)
    (indexedTransitionRawBool tromino periodicStrip)
    (stripSearchDepth periodicStrip) secondRemaining.pred first
  have edgeFit := edge tromino periodicStrip wellFormed
    first secondRemaining found
  have reachFit := reach tromino periodicStrip wellFormed
    first secondRemaining found firstBelow secondPositive secondBound
  have both := EvaluatorCodeFits.boolAnd edgeFit reachFit
  have bothTag :
      (if FiniteState.divideBoolTag edgeValue = 0 ∨
          FiniteState.divideBoolTag reachValue = 0 then 0 else 1) =
        FiniteState.divideBoolTag (edgeValue && reachValue) := by
    cases edgeValue <;> cases reachValue <;> rfl
  rw [bothTag] at both
  have old : EvaluatorCodeFits (Turing.ToPartrec.Code.get 5) values
      [FiniteState.divideBoolTag found]
      (EvaluatorCodeFits.getCost 5 values) := by
    simpa [values] using EvaluatorCodeFits.get 5 values
  have accumulated := EvaluatorCodeFits.boolOr old both
  have accumulatedTag :
      (if FiniteState.divideBoolTag found = 0 ∧
          FiniteState.divideBoolTag (edgeValue && reachValue) = 0
        then 0 else 1) =
        FiniteState.divideBoolTag (found || (edgeValue && reachValue)) := by
    cases found <;> cases edgeValue <;> cases reachValue <;> rfl
  rw [accumulatedTag] at accumulated
  simpa [candidateFoundCode, foundCost, values, edgeValue, reachValue,
    cycleCandidateBool] using accumulated

private theorem candidateFoundBudget_le (unit : Nat) (positive : 1 ≤ unit) :
    1000 * (1000 * (100000000 * unit + 1) + 1) ≤
      1000000000000000 * unit := by
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem foundCost_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (foundValue : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) :
    let inputLength :=
      ((Complexity.primcodableFinEncoding PeriodicStrip).encode
        periodicStrip).length
    let values :=
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining,
        FiniteState.divideBoolTag foundValue]
    foundCost tromino periodicStrip first secondRemaining foundValue values ≤
      1000000000000000 * candidateBaseUnit inputLength := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining,
      FiniteState.divideBoolTag foundValue]
  let edgeValue := indexedTransitionRawBool tromino periodicStrip
    first secondRemaining.pred
  let reachValue := FiniteState.divideReachIndexDFSBool
    (indexCount periodicStrip)
    (indexedTransitionRawBool tromino periodicStrip)
    (stripSearchDepth periodicStrip) secondRemaining.pred first
  let firstBudget := 100000000 * candidateBaseUnit inputLength
  have valuesLoop : encodedListSpace values ≤
      stripLoopPayloadSpaceBound inputLength := by
    simpa [values, inputLength] using candidateValuesSpace_le periodicStrip
      first secondRemaining foundValue firstBelow secondBound
  have basePositive : 1 ≤ candidateBaseUnit inputLength := by
    simp [candidateBaseUnit]
  have firstPositive : 1 ≤ firstBudget := by
    simp [firstBudget]
    omega
  have valuesBound : encodedListSpace values ≤ firstBudget := by
    simp [firstBudget, candidateBaseUnit]
    omega
  have valuesStrict : encodedListSpace values + 1 ≤ firstBudget := by
    simp [firstBudget, candidateBaseUnit]
    omega
  have headSpace := encodedListSpace_singleton_headI_le values
  have headBound :
      (Computability.encodeNat values.headI).length ≤ firstBudget := by
    simp [encodedListSpace_cons] at headSpace
    omega
  have headSuccessor := encodeNat_succ_length_le values.headI
  have headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ firstBudget := by
    simp only [Nat.succ_eq_add_one] at headSuccessor
    simp [encodedListSpace_cons] at headSpace
    omega
  have edgeBound :
      edgeCost tromino periodicStrip first secondRemaining values ≤
        firstBudget := by
    simpa [values, inputLength, firstBudget] using
      edgeCost_le tromino periodicStrip first secondRemaining foundValue
        firstBelow secondPositive secondBound
  have reachBound : reachCost periodicStrip values ≤ firstBudget := by
    simpa [values, inputLength, firstBudget] using
      reachCost_le periodicStrip first secondRemaining foundValue
        firstBelow secondBound
  have edgeValueBound : FiniteState.divideBoolTag edgeValue ≤ 1 := by
    cases edgeValue <;> decide
  have reachValueBound : FiniteState.divideBoolTag reachValue ≤ 1 := by
    cases reachValue <;> decide
  have both := EvaluatorCodeFits.boolAndCost_le_budget values
    (FiniteState.divideBoolTag edgeValue)
    (FiniteState.divideBoolTag reachValue)
    (edgeCost tromino periodicStrip first secondRemaining values)
    (reachCost periodicStrip values) firstBudget edgeValueBound
    reachValueBound valuesBound headBound headSuccessorBound edgeBound
    reachBound firstPositive
  let secondBudget := 1000 * (firstBudget + 1)
  have secondPositive : 1 ≤ secondBudget := by
    dsimp only [secondBudget]
    omega
  have firstSecond : firstBudget ≤ secondBudget := by
    simp [secondBudget]
    omega
  have valuesSecond := valuesBound.trans firstSecond
  have headSecond := headBound.trans firstSecond
  have headSuccessorSecond := headSuccessorBound.trans firstSecond
  have get5 := EvaluatorCodeFits.listCodeGetCost_le_linear 5 values
  have get5Bound : EvaluatorCodeFits.getCost 5 values ≤ secondBudget := by
    simp [secondBudget, firstBudget, candidateBaseUnit] at valuesLoop get5 ⊢
    omega
  have bothBound :
      EvaluatorCodeFits.boolAndCost values
          (FiniteState.divideBoolTag edgeValue)
          (FiniteState.divideBoolTag reachValue)
          (edgeCost tromino periodicStrip first secondRemaining values)
          (reachCost periodicStrip values) ≤ secondBudget := by
    simpa [secondBudget] using both
  have foundTagBound : FiniteState.divideBoolTag foundValue ≤ 1 := by
    cases foundValue <;> decide
  have bothTagBound :
      FiniteState.divideBoolTag (edgeValue && reachValue) ≤ 1 := by
    cases edgeValue <;> cases reachValue <;> decide
  have combined := EvaluatorCodeFits.boolOrCost_le_budget values
    (FiniteState.divideBoolTag foundValue)
    (FiniteState.divideBoolTag (edgeValue && reachValue))
    (EvaluatorCodeFits.getCost 5 values)
    (EvaluatorCodeFits.boolAndCost values
      (FiniteState.divideBoolTag edgeValue)
      (FiniteState.divideBoolTag reachValue)
      (edgeCost tromino periodicStrip first secondRemaining values)
      (reachCost periodicStrip values))
    secondBudget foundTagBound bothTagBound valuesSecond headSecond
    headSuccessorSecond get5Bound bothBound secondPositive
  have result :
      foundCost tromino periodicStrip first secondRemaining foundValue values ≤
        1000 * (secondBudget + 1) := by
    simpa [foundCost, edgeValue, reachValue] using combined
  apply result.trans
  dsimp only [secondBudget, firstBudget]
  exact candidateFoundBudget_le _ basePositive

private noncomputable def foundField
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (foundValue : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ indexCount periodicStrip)
    (values : List Nat)
    (valuesEq : values =
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining,
        FiniteState.divideBoolTag foundValue]) :
    StripSavitchStep.FieldFit values where
  code := candidateFoundCode tromino
  output := FiniteState.divideBoolTag
    (foundValue || cycleCandidateBool tromino periodicStrip
      (indexCount periodicStrip) (stripSearchDepth periodicStrip)
      first secondRemaining.pred)
  cost := foundCost tromino periodicStrip first secondRemaining
    foundValue values
  fits := by
    subst values
    exact found tromino periodicStrip wellFormed first secondRemaining
      foundValue firstBelow secondPositive secondBound

@[simp]
private theorem foundField_cost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (foundValue : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ indexCount periodicStrip)
    (values : List Nat)
    (valuesEq : values =
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining,
        FiniteState.divideBoolTag foundValue]) :
    (foundField tromino periodicStrip wellFormed first secondRemaining
      foundValue firstBelow secondPositive secondBound values valuesEq).cost =
        foundCost tromino periodicStrip first secondRemaining
          foundValue values := rfl

/-- Exact compositional evaluator cost of one complete second-endpoint
update. -/
noncomputable def stepCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (foundValue : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) : Nat :=
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining,
      FiniteState.divideBoolTag foundValue]
  StripSavitchStep.fieldsCost values
    [StripSavitchStep.getField 0 values,
      StripSavitchStep.getField 1 values,
      StripSavitchStep.getField 2 values,
      StripSavitchStep.getField 3 values,
      StripSavitchStep.predecessorField 4 values,
      foundField tromino periodicStrip wellFormed first secondRemaining
        foundValue firstBelow secondPositive secondBound values rfl]
    [] (EvaluatorCodeFits.nilCost values)

theorem exactStep
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (foundValue : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) :
    EvaluatorCodeFits (candidateStepCode tromino)
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining,
        FiniteState.divideBoolTag foundValue]
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining.pred,
        FiniteState.divideBoolTag
          (foundValue || cycleCandidateBool tromino periodicStrip
            (indexCount periodicStrip) (stripSearchDepth periodicStrip)
            first secondRemaining.pred)]
      (stepCost tromino periodicStrip wellFormed first secondRemaining
        foundValue firstBelow secondPositive secondBound) := by
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining,
      FiniteState.divideBoolTag foundValue]
  let resultField := foundField tromino periodicStrip wellFormed
    first secondRemaining foundValue firstBelow secondPositive secondBound
    values rfl
  have fit := StripSavitchStep.fields values
    [StripSavitchStep.getField 0 values,
      StripSavitchStep.getField 1 values,
      StripSavitchStep.getField 2 values,
      StripSavitchStep.getField 3 values,
      StripSavitchStep.predecessorField 4 values,
      resultField]
    (EvaluatorCodeFits.nil values)
  simpa [candidateStepCode, candidateSecond, stepCost,
    values, resultField, foundField,
    StripSavitchStep.fieldsCost,
    FiniteState.DivideEvalPartrec.fields,
    FiniteState.DivideEvalPartrec.field,
    FiniteState.DivideEvalPartrec.predecessorField,
    StripSavitchStep.getField,
    StripSavitchStep.predecessorField] using fit

private theorem candidateFieldsBudget_le
    (unit nil get0 get1 get2 get3 predecessor found : Nat)
    (positive : 1 ≤ unit)
    (nilBound : nil ≤ 1000 * unit)
    (get0Bound : get0 ≤ 10000 * unit)
    (get1Bound : get1 ≤ 20000 * unit)
    (get2Bound : get2 ≤ 30000 * unit)
    (get3Bound : get3 ≤ 40000 * unit)
    (predecessorBound : predecessor ≤ 30000000 * unit)
    (foundBound : found ≤ 1000000000000000 * unit) :
    nil + (get0 + get1 + get2 + get3 + predecessor + found) +
        6 * (3 * (unit + 2) + 2) ≤
      1000000000000000000 * unit := by
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
/-- One complete candidate update has a uniform polynomial-space cost. -/
theorem stepCost_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (foundValue : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) :
    stepCost tromino periodicStrip wellFormed first secondRemaining
        foundValue firstBelow secondPositive secondBound ≤
      stripCandidateStepSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  let foundResult :=
    foundValue || cycleCandidateBool tromino periodicStrip
      (indexCount periodicStrip) (stripSearchDepth periodicStrip)
      first secondRemaining.pred
  let values :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining,
      FiniteState.divideBoolTag foundValue]
  let output :=
    [Encodable.encode periodicStrip, indexCount periodicStrip,
      stripSearchDepth periodicStrip, first, secondRemaining.pred,
      FiniteState.divideBoolTag foundResult]
  have valuesBound : encodedListSpace values ≤
      stripLoopPayloadSpaceBound inputLength := by
    simpa [values, inputLength] using candidateValuesSpace_le periodicStrip
      first secondRemaining foundValue firstBelow secondBound
  have predecessorBound : secondRemaining.pred ≤ indexCount periodicStrip :=
    (Nat.pred_le secondRemaining).trans secondBound
  have outputBound : encodedListSpace output ≤
      stripLoopPayloadSpaceBound inputLength := by
    simpa [output, inputLength] using candidateValuesSpace_le periodicStrip
      first secondRemaining.pred foundResult firstBelow predecessorBound
  let unit := candidateBaseUnit inputLength
  have unitPositive : 1 ≤ unit := by
    simp [unit, candidateBaseUnit]
  have valuesUnit : encodedListSpace values ≤ unit := by
    simp [unit, candidateBaseUnit]
    omega
  have outputUnit : encodedListSpace output ≤ unit := by
    simp [unit, candidateBaseUnit]
    omega
  let resultField := foundField tromino periodicStrip wellFormed first
    secondRemaining foundValue firstBelow secondPositive secondBound values rfl
  let fieldFits : List (StripSavitchStep.FieldFit values) :=
    [StripSavitchStep.getField 0 values,
      StripSavitchStep.getField 1 values,
      StripSavitchStep.getField 2 values,
      StripSavitchStep.getField 3 values,
      StripSavitchStep.predecessorField 4 values,
      resultField]
  have outputEq : fieldFits.map StripSavitchStep.FieldFit.output = output := by
    simp [fieldFits, resultField, foundField, output, foundResult, values,
      StripSavitchStep.getField, StripSavitchStep.predecessorField]
  have assembled := StripSavitchStep.fieldsCost_le_of values fieldFits []
    (EvaluatorCodeFits.nilCost values) unit valuesUnit (by
      simpa [outputEq] using outputUnit)
  have get0 := EvaluatorCodeFits.listCodeGetCost_le_linear 0 values
  have get1 := EvaluatorCodeFits.listCodeGetCost_le_linear 1 values
  have get2 := EvaluatorCodeFits.listCodeGetCost_le_linear 2 values
  have get3 := EvaluatorCodeFits.listCodeGetCost_le_linear 3 values
  have pred4 := predecessorFieldCost_le_linear 4 values (by omega)
  have foundBound := foundCost_le tromino periodicStrip first
    secondRemaining foundValue firstBelow secondPositive secondBound
  have nil := nilCost_le_linear values
  have assembled' :
      stepCost tromino periodicStrip wellFormed first secondRemaining
          foundValue firstBelow secondPositive secondBound ≤
        EvaluatorCodeFits.nilCost values +
          (EvaluatorCodeFits.getCost 0 values +
            EvaluatorCodeFits.getCost 1 values +
            EvaluatorCodeFits.getCost 2 values +
            EvaluatorCodeFits.getCost 3 values +
            (StripSavitchStep.predecessorField 4 values).cost +
            foundCost tromino periodicStrip first secondRemaining
              foundValue values) +
          6 * (3 * (unit + 2) + 2) := by
    rw [show stepCost tromino periodicStrip wellFormed first secondRemaining
        foundValue firstBelow secondPositive secondBound =
      StripSavitchStep.fieldsCost values fieldFits []
        (EvaluatorCodeFits.nilCost values) by rfl]
    have costsEq :
        (fieldFits.map StripSavitchStep.FieldFit.cost).sum =
          EvaluatorCodeFits.getCost 0 values +
            EvaluatorCodeFits.getCost 1 values +
            EvaluatorCodeFits.getCost 2 values +
            EvaluatorCodeFits.getCost 3 values +
            (StripSavitchStep.predecessorField 4 values).cost +
            foundCost tromino periodicStrip first secondRemaining
              foundValue values := by
      simp only [fieldFits, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil,
        StripSavitchStep.getField_cost, resultField, foundField_cost]
      omega
    have lengthEq : fieldFits.length = 6 := by
      simp only [fieldFits, List.length_cons, List.length_nil]
    rw [costsEq, lengthEq] at assembled
    exact assembled
  have valuesPlus : encodedListSpace values + 1 ≤ unit := by
    simp [unit, candidateBaseUnit]
    omega
  have get0' : EvaluatorCodeFits.getCost 0 values ≤ 10000 * unit :=
    get0.trans (by omega)
  have get1' : EvaluatorCodeFits.getCost 1 values ≤ 20000 * unit := by
    simpa only [Nat.reduceAdd, Nat.reduceMul] using get1.trans (by gcongr)
  have get2' : EvaluatorCodeFits.getCost 2 values ≤ 30000 * unit := by
    simpa only [Nat.reduceAdd, Nat.reduceMul] using get2.trans (by gcongr)
  have get3' : EvaluatorCodeFits.getCost 3 values ≤ 40000 * unit := by
    simpa only [Nat.reduceAdd, Nat.reduceMul] using get3.trans (by gcongr)
  have pred4' : (StripSavitchStep.predecessorField 4 values).cost ≤
      30000000 * unit := pred4.trans (by gcongr)
  have nil' : EvaluatorCodeFits.nilCost values ≤ 1000 * unit :=
    nil.trans (by gcongr)
  have foundBound' :
      foundCost tromino periodicStrip first secondRemaining foundValue values ≤
        1000000000000000 * unit := by
    simpa [values, inputLength, unit] using foundBound
  apply assembled'.trans
  rw [show stripCandidateStepSpaceBound inputLength =
      1000000000000000000 * unit by rfl]
  exact candidateFieldsBudget_le unit _ _ _ _ _ _ _ unitPositive nil'
    get0' get1' get2' get3' pred4' foundBound'

/-- Polynomial-cost form of `exactStep`, ready for the inner endpoint
countdown. -/
theorem exactStep_polynomial
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (foundValue : Bool)
    (firstBelow : first < indexCount periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ indexCount periodicStrip) :
    EvaluatorCodeFits (candidateStepCode tromino)
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining,
        FiniteState.divideBoolTag foundValue]
      [Encodable.encode periodicStrip, indexCount periodicStrip,
        stripSearchDepth periodicStrip, first, secondRemaining.pred,
        FiniteState.divideBoolTag
          (foundValue || cycleCandidateBool tromino periodicStrip
            (indexCount periodicStrip) (stripSearchDepth periodicStrip)
            first secondRemaining.pred)]
      (stripCandidateStepSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length) :=
  (exactStep tromino periodicStrip wellFormed first secondRemaining foundValue
    firstBelow secondPositive secondBound).mono
      (stepCost_le tromino periodicStrip wellFormed first secondRemaining
        foundValue firstBelow secondPositive secondBound)

/-- Canonical six-field payload of the second-endpoint scan. -/
def payload (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool) : List Nat :=
  [Encodable.encode periodicStrip, indexCount periodicStrip,
    stripSearchDepth periodicStrip, first, secondRemaining,
    FiniteState.divideBoolTag found]

private def boolOfTag (value : Nat) : Bool := decide (value ≠ 0)

@[simp]
private theorem boolOfTag_divideBoolTag (found : Bool) :
    boolOfTag (FiniteState.divideBoolTag found) = found := by
  cases found <;> decide

/-- Total payload transformer corresponding to one candidate update.  Its
definition is total so it can serve as the semantic step supplied to the
generic flat-iteration space theorem; the reachable invariant below keeps it
on canonical six-field payloads. -/
def programStep (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first : Nat) (values : List Nat) : List Nat :=
  let secondRemaining := values[4]?.getD 0
  let found := boolOfTag (values[5]?.getD 0)
  payload periodicStrip first secondRemaining.pred
    (found || cycleCandidateBool tromino periodicStrip
      (indexCount periodicStrip) (stripSearchDepth periodicStrip)
      first secondRemaining.pred)

@[simp]
theorem programStep_payload
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool) :
    programStep tromino periodicStrip first
        (payload periodicStrip first secondRemaining found) =
      payload periodicStrip first secondRemaining.pred
        (found || cycleCandidateBool tromino periodicStrip
          (indexCount periodicStrip) (stripSearchDepth periodicStrip)
          first secondRemaining.pred) := by
  simp [programStep, payload]

/-- Iterating the total payload step over a synchronized countdown checks
exactly the endpoint indices below that countdown, in descending order. -/
theorem programStep_iterate
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first remaining : Nat) (found : Bool) :
    ((programStep tromino periodicStrip first)^[remaining])
        (payload periodicStrip first remaining found) =
      payload periodicStrip first 0
        (found || FiniteState.boundedAny
          (cycleCandidateBool tromino periodicStrip
            (indexCount periodicStrip) (stripSearchDepth periodicStrip)
            first)
          remaining) := by
  induction remaining generalizing found with
  | zero => simp [FiniteState.boundedAny]
  | succ remaining induction =>
      rw [Function.iterate_succ_apply]
      rw [programStep_payload]
      simpa [FiniteState.boundedAny, Bool.or_assoc] using
        induction
          (found || cycleCandidateBool tromino periodicStrip
            (indexCount periodicStrip) (stripSearchDepth periodicStrip)
            first remaining)

/-- Canonical payloads reachable while a synchronized second-endpoint
countdown is running. -/
def Reachable (periodicStrip : PeriodicStrip) (first : Nat)
    (remaining : Nat) (values : List Nat) : Prop :=
  ∃ found,
    values = payload periodicStrip first remaining found ∧
    remaining ≤ indexCount periodicStrip

theorem reachable_initial
    (periodicStrip : PeriodicStrip) (first : Nat) (found : Bool) :
    Reachable periodicStrip first (indexCount periodicStrip)
      (payload periodicStrip first (indexCount periodicStrip) found) :=
  ⟨found, rfl, Nat.le_refl _⟩

theorem reachable_step
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first remaining : Nat) (values : List Nat)
    (reachable : Reachable periodicStrip first (remaining + 1) values) :
    Reachable periodicStrip first remaining
      (programStep tromino periodicStrip first values) := by
  obtain ⟨found, rfl, bound⟩ := reachable
  refine ⟨found || cycleCandidateBool tromino periodicStrip
    (indexCount periodicStrip) (stripSearchDepth periodicStrip)
    first remaining, ?_, by omega⟩
  simpa using programStep_payload tromino periodicStrip first
    (remaining + 1) found

private theorem zeroBody
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first : Nat) (values : List Nat) :
    EvaluatorCodeFits
      (Turing.ToPartrec.Code.flatCountdownBody
        (candidateStepCode tromino))
      (0 :: values)
      (Turing.PartrecToTM2.flatCountdownOutput
        (programStep tromino periodicStrip first) 0 values)
      (flatCountdownBodyCost
        (programStep tromino periodicStrip first)
        (fun _ => stripCandidateStepSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length)
        0 values) := by
  simpa [Turing.ToPartrec.Code.flatCountdownBody,
    Turing.PartrecToTM2.flatCountdownOutput,
    flatCountdownBodyCost, EvaluatorCodeFits.zeroPrimeCost] using
      EvaluatorCodeFits.case_zero
        (successorBranch :=
          .cons Turing.ToPartrec.Code.one
            (.cons Turing.ToPartrec.Code.head
              ((candidateStepCode tromino).comp
                Turing.ToPartrec.Code.tail)))
        (values := 0 :: values) (by rfl)
        (EvaluatorCodeFits.zero'_named values)

private theorem bodyCost_le
    (inputLength remaining : Nat) (input output : List Nat)
    (inputBound :
      encodedListSpace (remaining :: input) ≤
        stripLoopPayloadSpaceBound inputLength)
    (outputBound :
      encodedListSpace output ≤
        stripLoopPayloadSpaceBound inputLength) :
    flatCountdownBodyCost (fun _ => output)
        (fun _ => stripCandidateStepSpaceBound inputLength)
        remaining input ≤
      stripCandidateBodySpaceBound inputLength := by
  cases remaining with
  | zero =>
      have inputTail := listCodeEncodedListSpace_tail_le (0 :: input)
      simp [flatCountdownBodyCost, EvaluatorCodeFits.zeroPrimeCost,
        stripCandidateBodySpaceBound, encodedListSpace_cons] at *
      omega
  | succ remaining =>
      let values := remaining :: input
      have predecessorBits := listCodeEncodeNat_length_mono
        (show remaining ≤ remaining + 1 by omega)
      have valuesBound : encodedListSpace values ≤
          stripLoopPayloadSpaceBound inputLength := by
        simp [values, encodedListSpace_cons] at inputBound ⊢
        omega
      have tailBound := EvaluatorCodeFits.listCodeTailCost_le_linear values
      have headBound := EvaluatorCodeFits.headCost_le values
      have zeroBound := EvaluatorCodeFits.listCodeZeroCost_le_linear values
      have successorZero := EvaluatorCodeFits.succCost_le [0]
      have remainingField :
          (Computability.encodeNat remaining).length + 1 ≤
            encodedListSpace values := by
        simp [values, encodedListSpace_cons]
      have outputWithCounter :
          encodedListSpace (remaining :: output) ≤
            2 * (stripLoopPayloadSpaceBound inputLength + 1) := by
        simp [encodedListSpace_cons] at outputBound ⊢
        omega
      have oneBits : (Computability.encodeNat 1).length = 1 := rfl
      have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
      simp [flatCountdownBodyCost, flatCountdownSuccBranchCost,
        EvaluatorCodeFits.prependCost, EvaluatorCodeFits.oneCost,
        values, stripCandidateBodySpaceBound,
        encodedListSpace_cons, encodedListSpace_nil, zeroBits, oneBits]
        at inputBound outputBound tailBound headBound zeroBound successorZero
          outputWithCounter ⊢
      omega

set_option maxHeartbeats 1000000 in
/-- The complete second-endpoint countdown reuses one polynomial body reserve
at every iteration. -/
theorem flatUniform
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first : Nat) (found : Bool)
    (firstBelow : first < indexCount periodicStrip) :
    EvaluatorCodeFits
      (Turing.ToPartrec.Code.flatIterate (candidateStepCode tromino))
      (indexCount periodicStrip ::
        payload periodicStrip first (indexCount periodicStrip) found)
      (payload periodicStrip first 0
        (found || FiniteState.boundedAny
          (cycleCandidateBool tromino periodicStrip
            (indexCount periodicStrip) (stripSearchDepth periodicStrip)
            first)
          (indexCount periodicStrip)))
      (stripCandidateBodySpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length) where
  input_space := by
    have input := stripCandidatePayload_encodedListSpace_le
      periodicStrip (indexCount periodicStrip) first
      (indexCount periodicStrip) found (Nat.le_refl _)
      (Nat.le_of_lt firstBelow) (Nat.le_refl _)
    have input' : encodedListSpace
        (indexCount periodicStrip ::
          payload periodicStrip first (indexCount periodicStrip) found) ≤
        stripLoopPayloadSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length := by
      simpa [payload] using input
    exact input'.trans (by
        simp [stripCandidateBodySpaceBound]
        omega)
  output_space := by
    have output := candidateValuesSpace_le periodicStrip first 0
      (found || FiniteState.boundedAny
        (cycleCandidateBool tromino periodicStrip
          (indexCount periodicStrip) (stripSearchDepth periodicStrip)
          first)
        (indexCount periodicStrip)) firstBelow (Nat.zero_le _)
    have output' : encodedListSpace
        (payload periodicStrip first 0
          (found || FiniteState.boundedAny
            (cycleCandidateBool tromino periodicStrip
              (indexCount periodicStrip) (stripSearchDepth periodicStrip)
              first)
            (indexCount periodicStrip))) ≤
        stripLoopPayloadSpaceBound
          ((Complexity.primcodableFinEncoding PeriodicStrip).encode
            periodicStrip).length := by
      simpa [payload] using output
    exact output'.trans (by
      simp [stripCandidateBodySpaceBound]
      omega)
  call continuation bound budget after := by
    let inputLength :=
      ((Complexity.primcodableFinEncoding PeriodicStrip).encode
        periodicStrip).length
    apply Turing.PartrecToTM2.EvaluatorCallFits.flatIterate_of_reachable_code_fits
      (step := programStep tromino periodicStrip first)
      (bodyCost := fun _ _ => stripCandidateBodySpaceBound inputLength)
      (invariant := Reachable periodicStrip first)
    · intro remaining values reachable
      obtain ⟨reachableFound, rfl, remainingBound⟩ := reachable
      cases remaining with
      | zero =>
          exact (zeroBody tromino periodicStrip first
            (payload periodicStrip first 0 reachableFound)).mono (by
              apply bodyCost_le inputLength 0
                (payload periodicStrip first 0 reachableFound)
                (payload periodicStrip first 0 reachableFound)
              · simpa [payload, inputLength] using
                  stripCandidatePayload_encodedListSpace_le periodicStrip
                    0 first 0 reachableFound (Nat.zero_le _)
                    (Nat.le_of_lt firstBelow) (Nat.zero_le _)
              · simpa [payload, inputLength] using
                  candidateValuesSpace_le periodicStrip first 0
                    reachableFound firstBelow (Nat.zero_le _))
      | succ remaining =>
          have step := exactStep_polynomial tromino periodicStrip wellFormed
            first (remaining + 1) reachableFound firstBelow (by omega)
            remainingBound
          have body := EvaluatorCodeFits.flatCountdownBody_of_fit step
            (remaining + 1)
          have bodyOutput :
              Turing.PartrecToTM2.flatCountdownOutput
                  (fun _ =>
                    [Encodable.encode periodicStrip, indexCount periodicStrip,
                      stripSearchDepth periodicStrip, first,
                      (remaining + 1).pred,
                      FiniteState.divideBoolTag
                        (reachableFound || cycleCandidateBool tromino
                          periodicStrip (indexCount periodicStrip)
                          (stripSearchDepth periodicStrip) first
                          (remaining + 1).pred)])
                  (remaining + 1)
                  [Encodable.encode periodicStrip, indexCount periodicStrip,
                    stripSearchDepth periodicStrip, first, remaining + 1,
                    FiniteState.divideBoolTag reachableFound] =
                Turing.PartrecToTM2.flatCountdownOutput
                  (programStep tromino periodicStrip first)
                  (remaining + 1)
                  [Encodable.encode periodicStrip, indexCount periodicStrip,
                    stripSearchDepth periodicStrip, first, remaining + 1,
                    FiniteState.divideBoolTag reachableFound] := by
            simp [Turing.PartrecToTM2.flatCountdownOutput, programStep, payload]
          rw [bodyOutput] at body
          apply body.mono
          apply bodyCost_le inputLength (remaining + 1)
            (payload periodicStrip first (remaining + 1) reachableFound)
            (payload periodicStrip first remaining
              (reachableFound || cycleCandidateBool tromino periodicStrip
                (indexCount periodicStrip) (stripSearchDepth periodicStrip)
                first remaining))
          · simpa [payload, inputLength] using
              stripCandidatePayload_encodedListSpace_le periodicStrip
                (remaining + 1) first (remaining + 1) reachableFound
                remainingBound (Nat.le_of_lt firstBelow) remainingBound
          · simpa [payload, inputLength] using
              candidateValuesSpace_le periodicStrip first remaining
                (reachableFound || cycleCandidateBool tromino periodicStrip
                  (indexCount periodicStrip) (stripSearchDepth periodicStrip)
                  first remaining)
                firstBelow (by omega)
    · exact reachable_initial periodicStrip first found
    · exact reachable_step tromino periodicStrip first
    · intro remaining values reachable
      simpa [inputLength] using budget
    · rw [programStep_iterate]
      exact after

end StripCandidateStep

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
