import LeanTrominoes.PartrecDiv2Parity
import LeanTrominoes.PartrecBinaryLengthSpace

/-!
# Evaluator-space certificate for quotient and parity

This is the unprojected form of the fitted binary-division loop.  It has the
same uniform loop budget as `binaryDiv2Code`.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def div2ParityCost (number : Nat) : Nat :=
  binaryDiv2Cost number

theorem div2Parity (number : Nat) :
    EvaluatorCodeFits Code.div2ParityCode [number]
      [number.div2, number.bodd.toNat]
      (div2ParityCost number) where
  input_space := by
    simp [div2ParityCost, binaryDiv2Cost]
    omega
  output_space := by
    have quotientLe : number.div2 ≤ number := by
      have identity := Nat.bodd_add_div2 number
      omega
    have quotientBits := encodeNat_length_mono quotientLe
    have parityLe : number.bodd.toNat ≤ 1 := by
      cases number.bodd <;> decide
    have parityBits := encodeNat_length_mono parityLe
    have oneBits :
        (Computability.encodeNat 1).length = 1 := rfl
    simp only [div2ParityCost, binaryDiv2Cost,
      encodedListSpace_cons, encodedListSpace_nil]
    omega
  call continuation bound budget after := by
    have flatCall :
        EvaluatorCallFits
          (Code.flatIterate Code.binaryDiv2ListStepCode)
          continuation [number, 0, 0] bound := by
      apply
        EvaluatorCallFits.flatIterate_of_code_fits_invariant
          (bodyCost := binaryDiv2BodyCost)
          (invariant := binaryDiv2Invariant number)
      · exact binaryDiv2Body
      · exact binaryDiv2Invariant_initial number
      · exact binaryDiv2Invariant_preserved number
      · intro remaining payload invariant
        have bodyCost :=
          binaryDiv2BodyCost_le_total
            number remaining payload invariant
        simp only [div2ParityCost] at budget
        omega
      · simpa [Code.binaryDiv2ListStep_iterate] using after
    let loopContinuation :=
      ToPartrec.Cont.comp
        (Code.flatIterate Code.binaryDiv2ListStepCode)
        continuation
    have afterInput :
        EvaluatorExecutionFits bound
          (.ret loopContinuation [number, 0, 0]) := by
      apply EvaluatorExecutionFits.ret_comp
      · simp only [continuationSpace_comp,
          div2ParityCost] at *
        have initialInvariant :=
          binaryDiv2Invariant_initial number
        have initialBody :=
          binaryDiv2Body number [0, 0]
        have initialCost :=
          binaryDiv2BodyCost_le_total number
            number [0, 0] initialInvariant
        have inputSpace := initialBody.input_space
        omega
      · exact flatCall
    have inputFits :=
      binaryDiv2InputCode [number]
    have inputLeCost :
        binaryDiv2InputCost [number] ≤
          div2ParityCost number := by
      have inputCost := binaryDiv2InputCost_le [number]
      simp only [div2ParityCost, binaryDiv2Cost]
      omega
    have inputBudget :
        binaryDiv2InputCost [number] +
            continuationSpace loopContinuation ≤
          bound := by
      simp only [loopContinuation,
        continuationSpace_comp]
      omega
    have inputCall :
        EvaluatorCallFits Code.binaryDiv2InputCode
          loopContinuation [number] bound :=
      inputFits.call loopContinuation bound
        inputBudget afterInput
    have whole := EvaluatorCallFits.comp inputCall
    simpa [Code.div2ParityCode,
      loopContinuation] using whole

end EvaluatorCodeFits

end PartrecToTM2
end Turing
