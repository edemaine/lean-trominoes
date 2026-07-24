import LeanTrominoes.StripFrontierCyclePartrec
import LeanTrominoes.StripFrontierIndexedSearchSpace

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

end RawWindowState
end PeriodicStrip
end LeanTrominoes
