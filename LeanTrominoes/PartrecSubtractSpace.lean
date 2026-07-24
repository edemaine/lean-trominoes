import LeanTrominoes.PartrecSubtract
import LeanTrominoes.PartrecListCodeSpace
import LeanTrominoes.PartrecBinaryLengthSpace

/-!
# Evaluator-space certificate for truncated subtraction

The countdown counter is bounded by the subtrahend and the singleton payload
only decreases from the minuend.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def predCost (values : List Nat) : Nat :=
  match values.headI with
  | 0 =>
      zeroCost values.tail +
        encodedListSpace values +
          encodedListSpace (Code.subtractStepList values) + 1
  | predecessor + 1 =>
      headCost (predecessor :: values.tail) +
        encodedListSpace values +
          encodedListSpace (Code.subtractStepList values) + 1

theorem pred_named (values : List Nat) :
    EvaluatorCodeFits Code.pred values
      (Code.subtractStepList values) (predCost values) := by
  cases values with
  | nil =>
      simpa [Code.pred, Code.subtractStepList,
        predCost] using
        EvaluatorCodeFits.case_zero
          (successorBranch := Code.head)
          (values := ([] : List Nat)) rfl (zero [])
  | cons value values =>
      cases value with
      | zero =>
          simpa [Code.pred, Code.subtractStepList,
            predCost] using
            EvaluatorCodeFits.case_zero
              (successorBranch := Code.head)
              (values := 0 :: values) rfl (zero values)
      | succ predecessor =>
          simpa [Code.pred, Code.subtractStepList,
            predCost] using
            EvaluatorCodeFits.case_succ
              (zeroBranch := Code.zero)
              (values := (predecessor + 1) :: values)
              (predecessor := predecessor)
              (by simp) (head (predecessor :: values))

def subtractBodyCost
    (remaining : Nat) (payload : List Nat) : Nat :=
  flatCountdownBodyCost Code.subtractStepList
    predCost remaining payload

theorem subtractBody (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.pred)
      (remaining :: payload)
      (flatCountdownOutput Code.subtractStepList
        remaining payload)
      (subtractBodyCost remaining payload) := by
  simpa [subtractBodyCost] using
    flatCountdownBody pred_named remaining payload

def subtractInputCost (minuend subtrahend : Nat) : Nat :=
  prependCost [minuend, subtrahend] [subtrahend]
    [minuend]
    (getCost 1 [minuend, subtrahend])
    (getCost 0 [minuend, subtrahend])

theorem subtractInput (minuend subtrahend : Nat) :
    EvaluatorCodeFits Code.subtractInputCode
      [minuend, subtrahend] [subtrahend, minuend]
      (subtractInputCost minuend subtrahend) := by
  simpa [Code.subtractInputCode, subtractInputCost,
    prependCost] using
    prepend (get 1 [minuend, subtrahend])
      (get 0 [minuend, subtrahend])

def subtractLoopCost (minuend subtrahend : Nat) : Nat :=
  1000000 *
    (encodedListSpace [minuend, subtrahend] + 1)

def SubtractInvariant
    (minuend subtrahend remaining : Nat)
    (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = subtrahend ∧
      payload = [minuend - processed]

theorem subtractInvariant_initial
    (minuend subtrahend : Nat) :
    SubtractInvariant minuend subtrahend
      subtrahend [minuend] := by
  exact ⟨0, by simp, by simp⟩

theorem subtractInvariant_preserved
    (minuend subtrahend remaining : Nat)
    (payload : List Nat)
    (invariant :
      SubtractInvariant minuend subtrahend
        (remaining + 1) payload) :
    SubtractInvariant minuend subtrahend remaining
      (Code.subtractStepList payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  simp [Code.subtractStepList]
  omega

theorem subtractBodyCost_le_loop
    (minuend subtrahend remaining : Nat)
    (payload : List Nat)
    (invariant :
      SubtractInvariant minuend subtrahend remaining payload) :
    subtractBodyCost remaining payload ≤
      subtractLoopCost minuend subtrahend := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  have remainingBound : remaining ≤ subtrahend := by omega
  have remainingBits :=
    encodeNat_length_mono remainingBound
  have valueBound : minuend - processed ≤ minuend :=
    Nat.sub_le _ _
  have valueBits := encodeNat_length_mono valueBound
  have valuePredBits :=
    encodeNat_length_mono
      ((Nat.pred_le (minuend - processed)).trans valueBound)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  cases remaining with
  | zero =>
      simp [subtractBodyCost, flatCountdownBodyCost,
        subtractLoopCost, zeroPrimeCost,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits]
      omega
  | succ remaining =>
      have currentRemainingBits :=
        encodeNat_length_mono
          (show remaining ≤ subtrahend by omega)
      have inputRemainingBits :=
        encodeNat_length_mono
          (show remaining + 1 ≤ subtrahend by omega)
      cases valueEq : minuend - processed with
      | zero =>
          simp [subtractBodyCost, flatCountdownBodyCost,
            flatCountdownSuccBranchCost, predCost,
            subtractLoopCost, prependCost, idCost, headCost,
            nilCost, oneCost, zeroCost, zeroPrimeCost,
            tailCost, succCost, Code.subtractStepList,
            encodedListSpace_cons, encodedListSpace_nil,
            zeroBits, oneBits] at *
          omega
      | succ predecessor =>
          have predecessorBits :=
            encodeNat_length_mono
              (show predecessor ≤ minuend by omega)
          have predecessorSuccessorBits :=
            encodeNat_length_mono
              (show predecessor + 1 ≤ minuend by omega)
          simp [subtractBodyCost, flatCountdownBodyCost,
            flatCountdownSuccBranchCost, predCost,
            subtractLoopCost, prependCost, idCost, headCost,
            nilCost, oneCost, zeroCost, zeroPrimeCost,
            tailCost, succCost, Code.subtractStepList,
            encodedListSpace_cons, encodedListSpace_nil,
            zeroBits, oneBits] at *
          omega

def subtractCost (minuend subtrahend : Nat) : Nat :=
  subtractInputCost minuend subtrahend +
    subtractLoopCost minuend subtrahend

theorem subtract (minuend subtrahend : Nat) :
    EvaluatorCodeFits Code.subtractCode
      [minuend, subtrahend] [minuend - subtrahend]
      (subtractCost minuend subtrahend) where
  input_space := by
    have inputSpace :=
      (subtractInput minuend subtrahend).input_space
    simp only [subtractCost, encodedListSpace_cons,
      encodedListSpace_nil] at inputSpace ⊢
    omega
  output_space := by
    have finalInvariant :
        SubtractInvariant minuend subtrahend 0
          [minuend - subtrahend] := by
      exact ⟨subtrahend, by simp, rfl⟩
    have bodyOutput :=
      (subtractBody 0 [minuend - subtrahend]).output_space
    have bodyBound :=
      subtractBodyCost_le_loop minuend subtrahend 0
        [minuend - subtrahend] finalInvariant
    simp [flatCountdownOutput, encodedListSpace_cons] at bodyOutput
    simp only [subtractCost, encodedListSpace_cons,
      encodedListSpace_nil]
    omega
  call continuation bound budget after := by
    have finalPayload :
        ((Code.subtractStepList)^[subtrahend]) [minuend] =
          [minuend - subtrahend] :=
      Code.subtractStepList_iterate subtrahend minuend
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate Code.pred)
          continuation [subtrahend, minuend] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := subtractBodyCost)
          (invariant :=
            SubtractInvariant minuend subtrahend)
      · exact subtractBody
      · exact subtractInvariant_initial minuend subtrahend
      · exact subtractInvariant_preserved minuend subtrahend
      · intro remaining payload invariant
        have bodyCost :=
          subtractBodyCost_le_loop minuend subtrahend
            remaining payload invariant
        simp only [subtractCost] at budget
        omega
      · rw [finalPayload]
        exact after
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate Code.pred) continuation
    have initialInvariant :=
      subtractInvariant_initial minuend subtrahend
    have initialSpace :
        encodedListSpace [subtrahend, minuend] ≤
          subtractLoopCost minuend subtrahend := by
      have bodyInput :=
        (subtractBody subtrahend [minuend]).input_space
      have bodyBound :=
        subtractBodyCost_le_loop minuend subtrahend
          subtrahend [minuend] initialInvariant
      exact bodyInput.trans bodyBound
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation [subtrahend, minuend]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp]
        simp only [subtractCost] at budget
        omega
      · exact flatCall
    have inputCall :=
      (subtractInput minuend subtrahend).call
        loopContinuation bound
        (by
          simp only [loopContinuation,
            continuationSpace_comp, subtractCost] at *
          omega)
        afterInput
    have whole := EvaluatorCallFits.comp inputCall
    simpa [Code.subtractCode, loopContinuation] using whole

end EvaluatorCodeFits

end PartrecToTM2
end Turing
