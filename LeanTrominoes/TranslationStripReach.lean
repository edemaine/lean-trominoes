/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripReach
import LeanTrominoes.TranslationStripSavitchRun

/-! # Orientation-restricted strip Reach certificates

The input adapters and relation-independent bounds reuse the existing strip solver.
-/

namespace LeanTrominoes.TranslationStrip.Savitch
open PolyominoStripWindow PolyominoStripWindow.Savitch

open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

def reachCode : Code := answerExpr.code.comp ((Code.flatIterate (DivideEvalPartrec.stepCode baseCode)).comp reachInputCode)

def finalState (cells : Bool → List Cell) (height bound bits first last : Nat) : DivideEvalState :=
  ((divideEvalStep (2^bits) (TranslationStrip.check cells height bound))^[divideEvalFuel (2^bits) bits])
    (divideEvalInitial bits first last)

theorem reach_eval (cells : Bool → List Cell) (height bound bits first last : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    reachCode.eval (reachRequest bits first last (suffix cells height bound)) =
      pure [divideBoolTag (divideReachIndexDFSBool (2^bits) (TranslationStrip.check cells height bound) bits first last)] := by
  have inputRun := reachInput_eval bits first last (suffix cells height bound)
  have loopRun := DivideEvalPartrec.flatIterate_stepCode_eval_suffix baseCode 0 (2^bits)
    (TranslationStrip.check cells height bound) (suffix cells height bound)
    (base_eval cells height bound bounded 0 (2^bits))
    (divideEvalFuel (2^bits) bits) (divideEvalInitial bits first last)
  have step : reachCode.eval (reachRequest bits first last (suffix cells height bound)) =
      answerExpr.code.eval (GenericSavitchStep.flatProgramList (suffix cells height bound) 0 (2^bits)
        (finalState cells height bound bits first last)) := by
    simp [reachCode,inputRun,GenericSavitchStep.flatProgramList,loopRun,Part.bind_eq_bind,finalState]
  rw [step,Expr.code_eval,answer_eval]
  rfl

def reachBudget (bits suffixSpace : Nat) : Nat :=
  answerCoefficient*(stateBudget bits suffixSpace+1)+countdownBudget bits suffixSpace+
    reachInputCoefficient*(requestBudget bits suffixSpace+fuelBits bits+1)

theorem reach_fits (cells : Bool → List Cell) (height bound bits first last : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (hf : first < 2^bits) (hl : last < 2^bits) :
    EvaluatorCodeFits reachCode (reachRequest bits first last (suffix cells height bound))
      [divideBoolTag (divideReachIndexDFSBool (2^bits) (TranslationStrip.check cells height bound) bits first last)]
      (reachBudget bits (encodedListSpace (suffix cells height bound))) := by
  let rest := suffix cells height bound
  let final := GenericSavitchStep.flatProgramList rest 0 (2^bits) (finalState cells height bound bits first last)
  have initial := reachInput_fits bits first last rest
  have loop := countdown_fits cells height bound bits first last bounded hf hl
  have answer := answerExpr.code_fits_automatic final (by simp [answerExpr,Expr.noPower])
  have eq : answerExpr.eval final = divideBoolTag (divideReachIndexDFSBool (2^bits) (TranslationStrip.check cells height bound) bits first last) :=
    answer_eval rest (2^bits) (finalState cells height bound bits first last)
  rw [eq] at answer
  have result := comp answer (comp loop initial)
  apply result.mono
  have hs := state_space_le rest (TranslationStrip.check cells height bound) bits first last (divideEvalFuel (2^bits) bits) hf hl
  have hi := request_space_le bits first last rest hf hl
  change encodedListSpace final ≤ stateBudget bits (encodedListSpace rest) at hs
  change answerCoefficient*(encodedListSpace final+1)+(countdownBudget bits (encodedListSpace rest)+
    reachInputCoefficient*reachInputUnit bits first last rest) ≤ reachBudget bits (encodedListSpace rest)
  unfold reachBudget reachInputUnit
  have hm := Nat.mul_le_mul_left answerCoefficient (Nat.add_le_add_right hs 1)
  have hn := Nat.mul_le_mul_left reachInputCoefficient (Nat.add_le_add_right hi (fuelBits bits+1))
  nlinarith

end LeanTrominoes.TranslationStrip.Savitch
