import LeanTrominoes.PartrecPowerTwo
import LeanTrominoes.PartrecFuelSpace

/-!
# Evaluator-space certificate for powers of two

The padded strip state bound is computed by repeated doubling.  Each doubling
reuses the fitted tail-style addition loop, and the outer countdown preserves
the invariant that its singleton payload is `2 ^ processed`.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def powerDoubleInputCost (values : List Nat) : Nat :=
  let restCost :=
    prependCost values [values.headI] [values.headI]
      (headCost values) (headCost values)
  prependCost values [0] [values.headI, values.headI]
    (zeroCost values) restCost

theorem powerDoubleInput (values : List Nat) :
    EvaluatorCodeFits Code.powerDoubleInputCode values
      [0, values.headI, values.headI]
      (powerDoubleInputCost values) := by
  have rest := prepend (head values) (head values)
  have result := prepend (zero values) rest
  simpa [Code.powerDoubleInputCode,
    powerDoubleInputCost, prependCost] using result

def powerDoubleCost (values : List Nat) : Nat :=
  let normalized := [0, values.headI, values.headI]
  let added := [0, values.headI, values.headI + values.headI]
  getCost 2 added +
    (fuelAddPreviousCost normalized +
      powerDoubleInputCost values)

theorem powerDouble (values : List Nat) :
    EvaluatorCodeFits Code.powerDoubleCode values
      (Code.powerDoubleList values)
      (powerDoubleCost values) := by
  have normalized := powerDoubleInput values
  have added :=
    fuelAddPrevious [0, values.headI, values.headI]
  have addition := comp added normalized
  have projected :=
    get 2 [0, values.headI, values.headI + values.headI]
  have result := comp projected addition
  convert result using 1
  · simp [Code.powerDoubleCode]
  · simp [Code.powerDoubleList]
    omega
  · simp [powerDoubleCost]

def powerTwoInputCost (values : List Nat) : Nat :=
  prependCost values [values.headI] [1]
    (headCost values) (oneCost values)

theorem powerTwoInput (values : List Nat) :
    EvaluatorCodeFits Code.powerTwoInputCode values
      [values.headI, 1] (powerTwoInputCost values) := by
  simpa [Code.powerTwoInputCode, powerTwoInputCost,
    prependCost] using
    prepend (head values) (one values)

def powerDoubleBodyCost
    (remaining : Nat) (payload : List Nat) : Nat :=
  flatCountdownBodyCost Code.powerDoubleList
    powerDoubleCost remaining payload

theorem powerDoubleBody
    (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.powerDoubleCode)
      (remaining :: payload)
      (flatCountdownOutput Code.powerDoubleList
        remaining payload)
      (powerDoubleBodyCost remaining payload) := by
  simpa [powerDoubleBodyCost] using
    flatCountdownBody powerDouble remaining payload

def powerDoubleBound (value : Nat) : Nat :=
  10000000000000000000000000 *
    (encodedListSpace [value] +
      encodedListSpace [2 * value] + 1)

theorem powerDoubleCost_le (value : Nat) :
    powerDoubleCost [value] ≤
      powerDoubleBound value := by
  have valueBound : value ≤ 2 * value := by omega
  have valueBits := encodeNat_length_mono valueBound
  have valueSuccessorBits :=
    encodeNat_succ_length_le value
  have valuePlusBits :
      (Computability.encodeNat (value + 1)).length ≤
        (Computability.encodeNat value).length + 1 := by
    simpa [Nat.succ_eq_add_one] using valueSuccessorBits
  have twiceSuccessorBits :=
    encodeNat_succ_length_le (2 * value)
  have twicePlusBits :
      (Computability.encodeNat (2 * value + 1)).length ≤
        (Computability.encodeNat (2 * value)).length + 1 := by
    simpa [Nat.succ_eq_add_one] using twiceSuccessorBits
  have twiceDirectBits :
      (Computability.encodeNat (value + value)).length =
        (Computability.encodeNat (2 * value)).length := by
    congr 2
    omega
  have twicePlusDirectBits :
      (Computability.encodeNat (value + value + 1)).length =
        (Computability.encodeNat (2 * value + 1)).length := by
    congr 2
    omega
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  simp [powerDoubleCost, powerDoubleBound,
    powerDoubleInputCost, fuelAddPreviousCost,
    fuelAddPreviousInputCost, fuelAddPreviousLoopCost,
    prependCost, getCost, dropCost, idCost, headCost,
    nilCost, zeroCost, zeroPrimeCost, tailCost,
    succCost, encodedListSpace_cons, encodedListSpace_nil,
    zeroBits, oneBits]
  omega

def powerTwoLoopCost (depth : Nat) : Nat :=
  100000000000000000000000000000000000000000000000000 *
    (3 * encodedListSpace [depth, 1] +
      3 * encodedListSpace [2 ^ depth] + 1)

def PowerTwoInvariant
    (depth remaining : Nat) (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = depth ∧
      payload = [2 ^ processed]

theorem powerTwoInvariant_initial (depth : Nat) :
    PowerTwoInvariant depth depth [1] := by
  exact ⟨0, by simp, by simp⟩

theorem powerTwoInvariant_preserved
    (depth remaining : Nat) (payload : List Nat)
    (invariant :
      PowerTwoInvariant depth (remaining + 1) payload) :
    PowerTwoInvariant depth remaining
      (Code.powerDoubleList payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  simp [Code.powerDoubleList, pow_succ]
  ring

theorem powerDoubleBodyCost_le_powerTwoLoopCost
    (depth remaining : Nat) (payload : List Nat)
    (invariant : PowerTwoInvariant depth remaining payload) :
    powerDoubleBodyCost remaining payload ≤
      powerTwoLoopCost depth := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  have processedBound : processed ≤ depth := by omega
  have currentBound : 2 ^ processed ≤ 2 ^ depth :=
    Nat.pow_le_pow_right (by omega) processedBound
  have currentBits := encodeNat_length_mono currentBound
  have currentSuccessorBits :=
    encodeNat_succ_length_le (2 ^ processed)
  have currentPlusBits :
      (Computability.encodeNat (2 ^ processed + 1)).length ≤
        (Computability.encodeNat (2 ^ processed)).length + 1 := by
    simpa [Nat.succ_eq_add_one] using currentSuccessorBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  cases remaining with
  | zero =>
      simp [powerDoubleBodyCost, flatCountdownBodyCost,
        powerTwoLoopCost, zeroPrimeCost,
        encodedListSpace_cons, encodedListSpace_nil, zeroBits]
      omega
  | succ remaining =>
      have nextProcessedBound : processed + 1 ≤ depth := by
        omega
      have nextBound : 2 ^ (processed + 1) ≤ 2 ^ depth :=
        Nat.pow_le_pow_right (by omega) nextProcessedBound
      have nextBits := encodeNat_length_mono nextBound
      have remainingBound : remaining ≤ depth := by omega
      have remainingBits := encodeNat_length_mono remainingBound
      have inputRemainingBound : remaining + 1 ≤ depth := by omega
      have inputRemainingBits :=
        encodeNat_length_mono inputRemainingBound
      have doubleDirectBits :
          (Computability.encodeNat (2 * 2 ^ processed)).length =
            (Computability.encodeNat (2 ^ (processed + 1))).length := by
        congr 2
        simp [pow_succ]
        ring
      have doubleSuccessorBits :=
        encodeNat_succ_length_le (2 * 2 ^ processed)
      have doublePlusBits :
          (Computability.encodeNat
            (2 * 2 ^ processed + 1)).length ≤
              (Computability.encodeNat
                (2 * 2 ^ processed)).length + 1 := by
        simpa [Nat.succ_eq_add_one] using doubleSuccessorBits
      have doubleCost :=
        powerDoubleCost_le (2 ^ processed)
      simp [powerDoubleBound, encodedListSpace_cons,
        encodedListSpace_nil] at doubleCost
      simp [powerDoubleBodyCost, flatCountdownBodyCost,
        flatCountdownSuccBranchCost, powerTwoLoopCost,
        prependCost, idCost, headCost, nilCost, oneCost,
        zeroCost, zeroPrimeCost, tailCost, succCost,
        Code.powerDoubleList, encodedListSpace_cons,
        encodedListSpace_nil, zeroBits, oneBits]
      omega

def powerTwoCost (depth : Nat) : Nat :=
  powerTwoInputCost [depth] +
    powerTwoLoopCost depth

theorem powerTwo (depth : Nat) :
    EvaluatorCodeFits Code.powerTwoCode [depth]
      [2 ^ depth] (powerTwoCost depth) where
  input_space := by
    have inputSpace := (powerTwoInput [depth]).input_space
    simp only [powerTwoCost]
    omega
  output_space := by
    simp [powerTwoCost, powerTwoLoopCost]
    omega
  call continuation bound budget after := by
    have budget' :
        powerTwoInputCost [depth] +
            powerTwoLoopCost depth +
            continuationSpace continuation ≤
          bound := by
      simpa [powerTwoCost] using budget
    have finalPayload :
        ((Code.powerDoubleList)^[depth]) [1] =
          [2 ^ depth] := by
      simpa using Code.powerDoubleList_iterate depth 1
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate Code.powerDoubleCode)
          continuation [depth, 1] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := powerDoubleBodyCost)
          (invariant := PowerTwoInvariant depth)
      · exact powerDoubleBody
      · exact powerTwoInvariant_initial depth
      · exact powerTwoInvariant_preserved depth
      · intro remaining payload invariant
        have bodyCost :=
          powerDoubleBodyCost_le_powerTwoLoopCost
            depth remaining payload invariant
        omega
      · rw [finalPayload]
        exact after
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate Code.powerDoubleCode)
        continuation
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation [depth, 1]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        have loopInputSpace :
            encodedListSpace [depth, 1] ≤
              powerTwoLoopCost depth := by
          simp [powerTwoLoopCost]
          omega
        omega
      · exact flatCall
    have inputCall :=
      (powerTwoInput [depth]).call
        loopContinuation bound
        (by
          simp only [loopContinuation,
            continuationSpace_comp]
          omega)
        afterInput
    have whole := EvaluatorCallFits.comp inputCall
    simpa [Code.powerTwoCode, loopContinuation] using whole

end EvaluatorCodeFits

end PartrecToTM2
end Turing
