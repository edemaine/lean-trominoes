/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripEvaluator
import LeanTrominoes.PolyominoStripBudgetPolynomial

/-! # Polynomial workspace in the original unary strip input length -/

namespace LeanTrominoes.Theorem55StripDecider.Evaluator
open Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits PolyominoStripWindow Polynomial

private theorem native_fields_space_le (values : List Nat) : encodedListSpace values ≤ values.sum+values.length := by
  induction values with
  | nil => rfl
  | cons n rest ih =>
    have hn := FiniteState.encodeNat_length_le_of_lt_pow n n n.lt_two_pow_self
    simp only [encodedListSpace_cons,List.sum_cons,List.length_cons]
    omega

theorem fields_space_le (input : Theorem55.StripInput) :
    encodedListSpace (fields input) ≤ 2*(Theorem55StripEncoding.finEncoding.encode input).length+8 := by
  have hb := bound_le_encoding_length input
  have hn := FiniteState.encodeNat_length_le_of_lt_pow (bound input) (bound input) (bound input).lt_two_pow_self
  have hf := native_fields_space_le (Theorem55StripEncoding.fields input)
  rw [← Theorem55StripEncoding.encoding_length] at hf
  simp only [fields,encodedListSpace_cons]
  omega

theorem suffix_space_le (input : Theorem55.StripInput) :
    encodedListSpace (Savitch.suffix (rawCells input) input.1 (bound input)) ≤
      suffixCoefficient*(2*(Theorem55StripEncoding.finEncoding.encode input).length+9) := by
  have h := (suffix_fits input).output_space
  exact h.trans (Nat.mul_le_mul_left suffixCoefficient (by have h' := fields_space_le input; omega))

def budgetEnvelope (bits space count inputSpace : Nat) : Nat :=
  let search := Savitch.cycleBudget bits space+Savitch.searchInputCoefficient*(space+bits+2)
  let body := 1000*(space+Savitch.cutCoefficient*(space+count+2)+search+2)
  guardBudget space (guardCoefficient*(space+1)) body+suffixCoefficient*(inputSpace+1)

theorem decisionBudget_eq (input : Theorem55.StripInput) :
    decisionBudget input = budgetEnvelope (stateBits Bool input.1 (bound input))
      (encodedListSpace (Savitch.suffix (rawCells input) input.1 (bound input))) input.2.length
      (encodedListSpace (fields input)) := rfl

theorem budgetEnvelope_mono {bits bits' space space' count count' inputSpace inputSpace' : Nat}
    (hb : bits ≤ bits') (hs : space ≤ space') (hc : count ≤ count') (hi : inputSpace ≤ inputSpace') :
    budgetEnvelope bits space count inputSpace ≤ budgetEnvelope bits' space' count' inputSpace' := by
  have hcycle := Savitch.cycleBudget_mono hb hs
  unfold budgetEnvelope guardBudget
  dsimp only
  gcongr

noncomputable def spacePolynomial : Polynomial Nat :=
  let bits := statePolynomial
  let space := C suffixCoefficient*(2*X+9)
  let search := Savitch.cycleBudgetPolynomial bits space+C Savitch.searchInputCoefficient*(space+bits+2)
  let body := 1000*(space+C Savitch.cutCoefficient*(space+X+2)+search+2)
  C guardCoefficient*(space+1)+body+10000*(space+1)+100*(space+2)+C suffixCoefficient*(2*X+9)

theorem spacePolynomial_eval (length : Nat) :
    spacePolynomial.eval length = budgetEnvelope (statePolynomial.eval length)
      (suffixCoefficient*(2*length+9)) length (2*length+8) := by
  simp only [spacePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_one,Polynomial.eval_ofNat,Polynomial.eval_X,Savitch.cycleBudgetPolynomial_eval,budgetEnvelope,guardBudget]
  ring

theorem decisionBudget_le (input : Theorem55.StripInput) :
    decisionBudget input ≤ spacePolynomial.eval (Theorem55StripEncoding.finEncoding.encode input).length := by
  rw [decisionBudget_eq,spacePolynomial_eval]
  exact budgetEnvelope_mono (stateBits_le input) (suffix_space_le input)
    (cellCount_le_encoding_length input) (fields_space_le input)

theorem decide_fits_polynomial (input : Theorem55.StripInput) :
    EvaluatorCodeFits decideCode (fields input) [(decideStripRaw input).toNat]
      (spacePolynomial.eval (Theorem55StripEncoding.finEncoding.encode input).length) :=
  (decide_fits input).mono (decisionBudget_le input)

end LeanTrominoes.Theorem55StripDecider.Evaluator
