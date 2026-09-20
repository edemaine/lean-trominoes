/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldSavitchRun
import LeanTrominoes.PolyominoStripReachInput

/-! # A complete certified CNF reachability program -/

namespace LeanTrominoes.PeriodicCNF.FieldSavitch
open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

def answerExpr : Expr := var 3-1
def answerCoefficient : Nat := answerExpr.weight*(answerExpr.radius+1)

def reachCode : Code := answerExpr.code.comp ((Code.flatIterate (DivideEvalPartrec.stepCode baseCode)).comp reachInputCode)

def finalState (f : PeriodicCNF Nat) (bits first last : Nat) : DivideEvalState :=
  ((divideEvalStep (2^bits) (FieldPredicate.check f))^[divideEvalFuel (2^bits) bits])
    (divideEvalInitial bits first last)

theorem answer_eval (rest : List Nat) (count : Nat) (state : DivideEvalState) :
    answerExpr.eval (GenericSavitchStep.flatProgramList rest 0 count state) =
      divideBoolTag (state.answer.getD false) := by
  change (divideOptionBoolTag state.answer)-1 = _
  cases state.answer with
  | none => rfl
  | some answer => cases answer <;> rfl

theorem reach_eval (f : PeriodicCNF Nat) (bits first last : Nat) :
    reachCode.eval (reachRequest bits first last (suffix f)) =
      pure [divideBoolTag (divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits first last)] := by
  have inputRun := reachInput_eval bits first last (suffix f)
  have loopRun := DivideEvalPartrec.flatIterate_stepCode_eval_suffix baseCode 0 (2^bits)
    (FieldPredicate.check f) (suffix f)
    (base_eval f 0 (2^bits))
    (divideEvalFuel (2^bits) bits) (divideEvalInitial bits first last)
  have step : reachCode.eval (reachRequest bits first last (suffix f)) =
      answerExpr.code.eval (GenericSavitchStep.flatProgramList (suffix f) 0 (2^bits)
        (finalState f bits first last)) := by
    simp [reachCode,inputRun,GenericSavitchStep.flatProgramList,loopRun,Part.bind_eq_bind,finalState]
  rw [step,Expr.code_eval,answer_eval]
  rfl

def requestBudget (bits suffixSpace : Nat) : Nat := 4*(bits+2)+suffixSpace

theorem request_space_le (bits first last : Nat) (rest : List Nat) (hf : first < 2^bits) (hl : last < 2^bits) :
    encodedListSpace (reachRequest bits first last rest) ≤ requestBudget bits (encodedListSpace rest) := by
  have countBits : (Computability.encodeNat (2^bits)).length ≤ bits+1 :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ (Nat.pow_lt_pow_right (by omega) (by omega))
  have depthBits : (Computability.encodeNat bits).length ≤ bits+1 :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ (bits.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
  have firstBits := FiniteState.encodeNat_length_le_of_lt_pow first bits hf
  have lastBits := FiniteState.encodeNat_length_le_of_lt_pow last bits hl
  simp [reachRequest,requestBudget,encodedListSpace_cons]
  omega

def reachBudget (bits suffixSpace : Nat) : Nat :=
  answerCoefficient*(stateBudget bits suffixSpace+1)+countdownBudget bits suffixSpace+
    reachInputCoefficient*(requestBudget bits suffixSpace+fuelBits bits+1)

theorem reach_fits (f : PeriodicCNF Nat) (bits first last : Nat)
    (hf : first < 2^bits) (hl : last < 2^bits) :
    EvaluatorCodeFits reachCode (reachRequest bits first last (suffix f))
      [divideBoolTag (divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits first last)]
      (reachBudget bits (encodedListSpace (suffix f))) := by
  let rest := suffix f
  let final := GenericSavitchStep.flatProgramList rest 0 (2^bits) (finalState f bits first last)
  have initial := reachInput_fits bits first last rest
  have loop := countdown_fits f bits first last hf hl
  have answer := answerExpr.code_fits_automatic final (by simp [answerExpr,Expr.noPower])
  have eq : answerExpr.eval final = divideBoolTag (divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits first last) :=
    answer_eval rest (2^bits) (finalState f bits first last)
  rw [eq] at answer
  have result := comp answer (comp loop initial)
  apply result.mono
  have hs := state_space_le rest (FieldPredicate.check f) bits first last (divideEvalFuel (2^bits) bits) hf hl
  have hi := request_space_le bits first last rest hf hl
  change encodedListSpace final ≤ stateBudget bits (encodedListSpace rest) at hs
  change answerCoefficient*(encodedListSpace final+1)+(countdownBudget bits (encodedListSpace rest)+
    reachInputCoefficient*reachInputUnit bits first last rest) ≤ reachBudget bits (encodedListSpace rest)
  unfold reachBudget reachInputUnit
  have hm := Nat.mul_le_mul_left answerCoefficient (Nat.add_le_add_right hs 1)
  have hn := Nat.mul_le_mul_left reachInputCoefficient (Nat.add_le_add_right hi (fuelBits bits+1))
  nlinarith

end LeanTrominoes.PeriodicCNF.FieldSavitch
