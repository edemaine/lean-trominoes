/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneFieldTransition
import LeanTrominoes.PolyominoStripCycleSearch
import LeanTrominoes.PartrecFlatSavitchContextSpace
import LeanTrominoes.PartrecLinearAdaptersSpace

/-! # Restore the exact-one checker input from a Savitch stack -/

namespace LeanTrominoes.PeriodicCNF.ExactOneFieldSavitch
set_option maxHeartbeats 200000
open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState

/-- The saved CNF context has zero placeholders for the two changing words. -/
def suffix (f : PeriodicCNF Nat) : List Nat := FieldPredicate.input f 0 0

def restoreInputCode : Code :=
  Code.prepend ((Code.get 0).comp DivideEvalPartrec.flatContextCode)
    (Code.prepend ((Code.get 1).comp DivideEvalPartrec.flatContextCode)
      (Code.prepend ((Code.get 2).comp DivideEvalPartrec.flatContextCode)
        (Code.prepend (Code.get 5) (Code.prepend (Code.get 6)
          ((Code.drop 5).comp DivideEvalPartrec.flatContextCode)))))

def restoreCoefficient : Nat :=
  4*(projectCoefficient 0+4*(projectCoefficient 1+4*(projectCoefficient 2+
    4*(60000+4*(70000+projectCoefficient 5+1)+1)+1)+1)+1)

theorem restoreInput_eval (f : PeriodicCNF Nat) (context count : Nat) (state : DivideEvalState) :
    restoreInputCode.eval (divideEvalProgramList context count state ++ suffix f) =
      pure (FieldPredicate.input f state.query.first state.query.last) := by
  have ctx := DivideEvalPartrec.flatContextCode_eval context count state (suffix f)
  simp only [restoreInputCode,Code.prepend_eval_eq,Code.eval,ctx,Part.bind_eq_bind,Part.bind_some]
  simp [suffix,FieldPredicate.input,FieldPredicate.context,divideEvalProgramList,DivideEvalState.toNatList]

theorem restoreInput_fits (f : PeriodicCNF Nat) (context count : Nat) (state : DivideEvalState) :
    EvaluatorCodeFits restoreInputCode (divideEvalProgramList context count state ++ suffix f)
      (FieldPredicate.input f state.query.first state.query.last)
      (restoreCoefficient*(encodedListSpace (divideEvalProgramList context count state ++ suffix f)+1)) := by
  let values := divideEvalProgramList context count state ++ suffix f
  have cf := context_fits context count state (suffix f)
  have h0 := comp_linear (get_linear 0 (suffix f)) cf
  have h1 := comp_linear (get_linear 1 (suffix f)) cf
  have h2 := comp_linear (get_linear 2 (suffix f)) cf
  have rest := comp_linear (drop_linear 5 (suffix f)) cf
  have result := prepend_linear h0 (prepend_linear h1 (prepend_linear h2
    (prepend_linear (get_linear 5 values) (prepend_linear (get_linear 6 values) rest))))
  change EvaluatorCodeFits restoreInputCode values
    (FieldPredicate.input f state.query.first state.query.last)
    (restoreCoefficient*(encodedListSpace values+1)) at result
  exact result

end LeanTrominoes.PeriodicCNF.ExactOneFieldSavitch
