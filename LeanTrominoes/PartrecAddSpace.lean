import LeanTrominoes.PartrecAdd
import LeanTrominoes.PartrecBinaryLengthSpace
import LeanTrominoes.PartrecFlatIterationSpace
import LeanTrominoes.PartrecListCodeSpace

/-!
# Evaluator-space certificate for natural addition

The countdown is bounded by the right input, while the singleton accumulator
grows monotonically from the left input to their sum.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def natAddStepCost (values : List Nat) : Nat :=
  succCost values

theorem natAddStep (values : List Nat) :
    EvaluatorCodeFits Code.succ values
      (Code.natAddStepList values)
      (natAddStepCost values) := by
  simpa [Code.natAddStepList, natAddStepCost] using
    succ_named values

def natAddBodyCost
    (remaining : Nat) (payload : List Nat) : Nat :=
  flatCountdownBodyCost Code.natAddStepList
    natAddStepCost remaining payload

theorem natAddBody (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.succ)
      (remaining :: payload)
      (flatCountdownOutput Code.natAddStepList
        remaining payload)
      (natAddBodyCost remaining payload) := by
  simpa [natAddBodyCost] using
    flatCountdownBody natAddStep remaining payload

def natAddInputCost (left right : Nat) : Nat :=
  prependCost [left, right] [right] [left]
    (getCost 1 [left, right])
    (getCost 0 [left, right])

theorem natAddInput (left right : Nat) :
    EvaluatorCodeFits Code.natAddInputCode
      [left, right] [right, left]
      (natAddInputCost left right) := by
  simpa [Code.natAddInputCode, natAddInputCost,
    prependCost] using
    prepend (get 1 [left, right])
      (get 0 [left, right])

def NatAddInvariant
    (left right remaining : Nat)
    (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = right ∧
      payload = [left + processed]

theorem natAddInvariant_initial (left right : Nat) :
    NatAddInvariant left right right [left] := by
  exact ⟨0, by simp, by simp⟩

theorem natAddInvariant_preserved
    (left right remaining : Nat)
    (payload : List Nat)
    (invariant :
      NatAddInvariant left right (remaining + 1) payload) :
    NatAddInvariant left right remaining
      (Code.natAddStepList payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  simp [Code.natAddStepList]
  omega

def natAddLoopCost (left right : Nat) : Nat :=
  1000000 *
    (encodedListSpace [left, right, left + right] + 1)

theorem natAddBodyCost_le_loop
    (left right remaining : Nat)
    (payload : List Nat)
    (invariant :
      NatAddInvariant left right remaining payload) :
    natAddBodyCost remaining payload ≤
      natAddLoopCost left right := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  have remainingBound : remaining ≤ right := by omega
  have remainingBits :=
    encodeNat_length_mono remainingBound
  have accumulatorBound :
      left + processed ≤ left + right := by omega
  have accumulatorBits :=
    encodeNat_length_mono accumulatorBound
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  cases remaining with
  | zero =>
      simp [natAddBodyCost, flatCountdownBodyCost,
        natAddLoopCost, zeroPrimeCost,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits]
      omega
  | succ remaining =>
      have accumulatorSuccBound :
          left + processed + 1 ≤ left + right := by
        omega
      have accumulatorSuccBits :=
        encodeNat_length_mono accumulatorSuccBound
      have currentRemainingBits :=
        encodeNat_length_mono
          (show remaining ≤ right by omega)
      have inputRemainingBits :=
        encodeNat_length_mono
          (show remaining + 1 ≤ right by omega)
      simp [natAddBodyCost, flatCountdownBodyCost,
        flatCountdownSuccBranchCost, natAddStepCost,
        natAddLoopCost, prependCost, idCost, headCost,
        nilCost, oneCost, zeroCost, zeroPrimeCost,
        tailCost, succCost, Code.natAddStepList,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] at *
      omega

def natAddCost (left right : Nat) : Nat :=
  natAddInputCost left right +
    natAddLoopCost left right

theorem natAdd (left right : Nat) :
    EvaluatorCodeFits Code.natAddCode
      [left, right] [left + right]
      (natAddCost left right) where
  input_space := by
    have inputSpace :=
      (natAddInput left right).input_space
    simp only [natAddCost, encodedListSpace_cons,
      encodedListSpace_nil] at inputSpace ⊢
    omega
  output_space := by
    have finalInvariant :
        NatAddInvariant left right 0 [left + right] := by
      exact ⟨right, by simp, rfl⟩
    have bodyOutput :=
      (natAddBody 0 [left + right]).output_space
    have bodyBound :=
      natAddBodyCost_le_loop left right 0
        [left + right] finalInvariant
    simp [flatCountdownOutput, encodedListSpace_cons] at bodyOutput
    simp only [natAddCost, encodedListSpace_cons,
      encodedListSpace_nil]
    omega
  call continuation bound budget after := by
    have finalPayload :
        (Code.natAddStepList^[right]) [left] =
          [left + right] :=
      Code.natAddStepList_iterate right left
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate Code.succ)
          continuation [right, left] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := natAddBodyCost)
          (invariant := NatAddInvariant left right)
      · exact natAddBody
      · exact natAddInvariant_initial left right
      · exact natAddInvariant_preserved left right
      · intro remaining payload invariant
        have bodyCost :=
          natAddBodyCost_le_loop left right
            remaining payload invariant
        simp only [natAddCost] at budget
        omega
      · rw [finalPayload]
        exact after
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate Code.succ) continuation
    have initialInvariant :=
      natAddInvariant_initial left right
    have initialSpace :
        encodedListSpace [right, left] ≤
          natAddLoopCost left right := by
      have bodyInput :=
        (natAddBody right [left]).input_space
      have bodyBound :=
        natAddBodyCost_le_loop left right
          right [left] initialInvariant
      exact bodyInput.trans bodyBound
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation [right, left]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        simp only [natAddCost] at budget
        omega
      · exact flatCall
    have inputCall :=
      (natAddInput left right).call
        loopContinuation bound
        (by
          simp only [loopContinuation,
            continuationSpace_comp, natAddCost] at *
          omega)
        afterInput
    have whole := EvaluatorCallFits.comp inputCall
    simpa [Code.natAddCode, loopContinuation] using whole

end EvaluatorCodeFits

end PartrecToTM2
end Turing
