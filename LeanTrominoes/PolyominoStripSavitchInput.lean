/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripTransitionExprSpace
import LeanTrominoes.PartrecFlatSavitchContextSpace
import LeanTrominoes.PartrecLinearAdaptersSpace

/-! # Restore the strip checker input from a Savitch stack -/

namespace LeanTrominoes.PolyominoStripWindow.Savitch
set_option maxHeartbeats 200000
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState

/-- The saved strip context has zero placeholders for the two changing words. -/
def suffix (cells : Bool → List Cell) (height bound : Nat) : List Nat := Arithmetic.input cells height bound 0 0

def contextCoefficient : Nat := 10000000000000000000000000000000000000000000000000000000000000000

def projectCoefficient (index : Nat) : Nat :=
  (10000*(index+1))*(contextCoefficient+1)+contextCoefficient

def restoreInputCode : Code :=
  Code.prepend ((Code.get 0).comp DivideEvalPartrec.flatContextCode)
    (Code.prepend ((Code.get 1).comp DivideEvalPartrec.flatContextCode)
      (Code.prepend (Code.get 5) (Code.prepend (Code.get 6)
        ((Code.drop 4).comp DivideEvalPartrec.flatContextCode))))

def restoreCoefficient : Nat :=
  4*(projectCoefficient 0+4*(projectCoefficient 1+
    4*(60000+4*(70000+projectCoefficient 4+1)+1)+1)+1)

theorem context_fits (context count : Nat) (state : DivideEvalState) (rest : List Nat) :
    EvaluatorCodeFits DivideEvalPartrec.flatContextCode (divideEvalProgramList context count state ++ rest)
      rest (contextCoefficient*(encodedListSpace (divideEvalProgramList context count state ++ rest)+1)) := by
  apply (flatContextBounded context count state rest).mono
  simp only [flatContextSpaceBound,flatContextSpaceUnit,contextCoefficient]
  omega

theorem restoreInput_eval (cells : Bool → List Cell) (height bound context count : Nat) (state : DivideEvalState) :
    restoreInputCode.eval (divideEvalProgramList context count state ++ suffix cells height bound) =
      pure (Arithmetic.input cells height bound state.query.first state.query.last) := by
  have ctx := DivideEvalPartrec.flatContextCode_eval context count state (suffix cells height bound)
  simp only [restoreInputCode,Code.prepend_eval_eq,Code.eval,ctx,Part.bind_eq_bind,Part.bind_some]
  simp [suffix,Arithmetic.input,divideEvalProgramList,DivideEvalState.toNatList]

theorem restoreInput_fits (cells : Bool → List Cell) (height bound context count : Nat) (state : DivideEvalState) :
    EvaluatorCodeFits restoreInputCode (divideEvalProgramList context count state ++ suffix cells height bound)
      (Arithmetic.input cells height bound state.query.first state.query.last)
      (restoreCoefficient*(encodedListSpace (divideEvalProgramList context count state ++ suffix cells height bound)+1)) := by
  let values := divideEvalProgramList context count state ++ suffix cells height bound
  have cf := context_fits context count state (suffix cells height bound)
  have h0 := comp_linear (get_linear 0 (suffix cells height bound)) cf
  have h1 := comp_linear (get_linear 1 (suffix cells height bound)) cf
  have rest := comp_linear (drop_linear 4 (suffix cells height bound)) cf
  have result := prepend_linear h0 (prepend_linear h1
    (prepend_linear (get_linear 5 values) (prepend_linear (get_linear 6 values) rest)))
  change EvaluatorCodeFits restoreInputCode values
    (Arithmetic.input cells height bound state.query.first state.query.last)
    (restoreCoefficient*(encodedListSpace values+1)) at result
  exact result

end LeanTrominoes.PolyominoStripWindow.Savitch
