/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedAllSpace
import LeanTrominoes.PartrecBinaryLengthSpace

/-! # A uniform space allowance for iteration along a certified orbit -/

namespace Turing.PartrecToTM2.EvaluatorCodeFits
open ToPartrec

def iterationBudget (stepBudget counterBits : Nat) : Nat := 100000*(stepBudget+counterBits+1)

theorem countdownBodyCost_le (remaining : Nat) (payload output : List Nat) (cost budget bits : Nat)
    (inputBound : encodedListSpace payload ≤ budget) (outputBound : encodedListSpace output ≤ budget)
    (stepBound : cost ≤ budget) (counterBound : (Computability.encodeNat remaining).length ≤ bits) :
    flatCountdownBodyCost (fun _ => output) (fun _ => cost) remaining payload ≤ iterationBudget budget bits := by
  cases remaining with
  | zero =>
    simp [flatCountdownBodyCost,zeroPrimeCost,iterationBudget,encodedListSpace_cons] at *
    omega
  | succ remaining =>
    let values := remaining :: payload
    have predecessorBits := listCodeEncodeNat_length_mono (show remaining ≤ remaining+1 by omega)
    have valuesBound : encodedListSpace values ≤ budget+bits+1 := by
      simp only [values,encodedListSpace_cons]
      omega
    have tailBound := listCodeTailCost_le_linear values
    have headBound := headCost_le values
    have zeroBound := listCodeZeroCost_le_linear values
    have successorZero := succCost_le [0]
    have remainingField : (Computability.encodeNat remaining).length+1 ≤ encodedListSpace values := by
      simp [values,encodedListSpace_cons]
    have outputWithCounter : encodedListSpace (remaining :: output) ≤ budget+bits+1 := by
      simp only [encodedListSpace_cons]
      omega
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    simp [flatCountdownBodyCost,flatCountdownSuccBranchCost,prependCost,oneCost,values,
      iterationBudget,encodedListSpace_cons,encodedListSpace_nil,zeroBits,oneBits] at inputBound outputBound stepBound tailBound headBound zeroBound successorZero outputWithCounter valuesBound ⊢
    omega

/-- Only states reached from the given payload need a one-step certificate. -/
theorem flatIterate_uniform (code : Code) (step : List Nat → List Nat) (payload : List Nat)
    (count stepBudget counterBits : Nat)
    (countBits : (Computability.encodeNat count).length ≤ counterBits)
    (fits : ∀ taken ≤ count, EvaluatorCodeFits code ((step^[taken]) payload)
      ((step^[taken+1]) payload) stepBudget) :
    EvaluatorCodeFits (Code.flatIterate code) (count :: payload) ((step^[count]) payload)
      (iterationBudget stepBudget counterBits) where
  input_space := by
    have h := (fits 0 (by omega)).input_space
    simp only [Function.iterate_zero, id_eq] at h
    simp only [encodedListSpace_cons,iterationBudget]
    omega
  output_space := by
    have h := (fits count le_rfl).input_space
    simp only [iterationBudget]
    omega
  call continuation bound budget after := by
    apply EvaluatorCallFits.flatIterate_of_reachable_code_fits
      (step := step) (bodyCost := fun _ _ => iterationBudget stepBudget counterBits)
      (invariant := fun remaining values => ∃ taken, remaining+taken=count ∧ values=(step^[taken]) payload)
    · intro remaining values reachable
      obtain ⟨taken,total,rfl⟩ := reachable
      have fit := fits taken (by omega)
      rw [Function.iterate_succ_apply'] at fit
      have body := flatCountdownBody_of_fit fit remaining
      have body' : EvaluatorCodeFits (Code.flatCountdownBody code)
          (remaining :: (step^[taken]) payload)
          (flatCountdownOutput step remaining ((step^[taken]) payload))
          (flatCountdownBodyCost (fun _ => step ((step^[taken]) payload)) (fun _ => stepBudget)
            remaining ((step^[taken]) payload)) := by
        cases remaining <;> simpa [flatCountdownOutput] using body
      apply body'.mono
      exact countdownBodyCost_le remaining _ _ stepBudget stepBudget counterBits
        fit.input_space fit.output_space le_rfl
        ((listCodeEncodeNat_length_mono (show remaining ≤ count by omega)).trans countBits)
    · exact ⟨0,by omega,rfl⟩
    · intro remaining values reachable
      obtain ⟨taken,total,rfl⟩ := reachable
      exact ⟨taken+1,by omega,(Function.iterate_succ_apply' step taken payload).symm⟩
    · intro remaining values reachable
      exact budget
    · exact after

end Turing.PartrecToTM2.EvaluatorCodeFits
