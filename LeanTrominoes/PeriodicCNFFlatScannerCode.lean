/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFlatScanner
import LeanTrominoes.BoundedArithmeticLogic

/-! # Executable flat CNF scanning in the partial-recursive evaluator -/
namespace LeanTrominoes.PeriodicCNF.FlatScanner
open Turing.ToPartrec BoundedArithmetic BoundedArithmetic.Expr

/-- Compile a fixed list of scalar expressions followed by an unread suffix. -/
def outputCode : List Expr → Nat → Code
  | [], skip => Code.drop skip
  | e :: es, skip => Code.prepend e.code (outputCode es skip)

theorem outputCode_eval (es : List Expr) (skip : Nat) (v : List Nat) :
    (outputCode es skip).eval v = pure (es.map (fun e => e.eval v) ++ v.drop skip) := by
  induction es with
  | nil => simp [outputCode]
  | cons e es ih => simp [outputCode,Expr.code_eval,ih,Part.bind_eq_bind]

def clauseCode : Code := outputCode
  [var 0+1,var 5,var 2-1,var 3+.powerTwo (var 0),var 4] 6

def literalCode : Code := outputCode
  [var 0+4,var 1-1,var 2,var 3,var 4+.powerTwo (var 0)] 9

def stepCode : Code := Code.branchZero (Code.get 1)
  (Code.branchZero (Code.get 2) Code.id clauseCode) literalCode

theorem stepCode_eval (v : List Nat) : stepCode.eval v = pure (step v) := by
  have hc : clauseCode.eval v = pure
      ([v[0]?.getD 0+1,v[5]?.getD 0,v[2]?.getD 0-1,
        v[3]?.getD 0+2^(v[0]?.getD 0),v[4]?.getD 0] ++ v.drop 6) := by
    simp [clauseCode,outputCode_eval,Expr.eval,Op.eval]
  have hl : literalCode.eval v = pure
      ([v[0]?.getD 0+4,v[1]?.getD 0-1,v[2]?.getD 0,
        v[3]?.getD 0,v[4]?.getD 0+2^(v[0]?.getD 0)] ++ v.drop 9) := by
    simp [literalCode,outputCode_eval,Expr.eval,Op.eval]
  by_cases h1 : v[1]?.getD 0 = 0
  · have branch : (Code.branchZero (Code.get 2) Code.id clauseCode).eval v = pure (step v) := by
      by_cases h2 : v[2]?.getD 0 = 0
      · simpa [step,h1,h2] using Code.branchZero_eval_zero_at
          (Code.get 2) Code.id clauseCode v _ (Code.get_eval _ _) v (Code.id_eval _) h2
      · simpa [step,h1,h2] using Code.branchZero_eval_succ_at
          (Code.get 2) Code.id clauseCode v _ (Code.get_eval _ _) _ hc (Nat.pos_of_ne_zero h2)
    exact Code.branchZero_eval_zero_at (Code.get 1) _ _ v _ (Code.get_eval _ _) _ branch h1
  · simpa [stepCode,step,h1] using Code.branchZero_eval_succ_at
      (Code.get 1) (Code.branchZero (Code.get 2) Code.id clauseCode) literalCode
      v _ (Code.get_eval _ _) _ hl (Nat.pos_of_ne_zero h1)

/-- The countdown scanner uses the number of input fields as its iteration budget. -/
theorem scanCode_eval (f : PeriodicCNF Nat) :
    (Code.flatIterate stepCode).eval
      ((PeriodicCNFFlatEncoding.formulaFields f).length :: (initial f).fields) =
    pure [(scan f).cursor,0,0,(scan f).clauseMask,(scan f).literalMask] := by
  rw [Code.flatIterate_eval stepCode step stepCode_eval,iterate_fields]
  change pure (scan f).fields = _
  simp [State.fields,State.pending,(scan_finished f).1,(scan_finished f).2]

end LeanTrominoes.PeriodicCNF.FlatScanner
