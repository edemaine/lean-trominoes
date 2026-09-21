/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteGeometry
import LeanTrominoes.PeriodicGraphCoreData

/-! # Signed clause-anchor offsets in the endpoint query -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry
open RouteInput PeriodicCNFFlatEncoding PeriodicCNF.FlatScanner

theorem offset_eval (input : Input Nat) (front : List Nat) (literal header : Expr)
    (h : Nat) (c : PeriodicClause Nat) (hc : (h,c)∈clauseEntries 1 input.1.clauses)
    (i : Nat) (hi : i<c.length)
    (hl : literal.eval (front++context input)=h+1+4*i)
    (hh : header.eval (front++context input)=h) :
    pointEval (offset front.length literal header) (front++context input) =
      Cell.sub c[i].offset (PeriodicCNF.clauseAnchor c) := by
  have hn : 0<c.length := by omega
  have coord (j : Nat) (hj : j<c.length) (axis : Fin 2) :
      (formulaFields input.1)[h+1+4*j+(axis.val+1)]?.getD 0 =
        Encodable.encode (if axis.val=0 then c[j].offset.1 else c[j].offset.2) := by
    have e := congrArg (fun x : Option Nat => x.getD 0)
      (clauseEntry_literal input.1 hc j hj (axis.val+1) (by have := axis.isLt; omega))
    fin_cases axis <;> simpa [literalFields] using e
  have lx : (formulaField front.length (literal+1)).eval (front++context input)=Encodable.encode c[i].offset.1 := by
    rw [formulaField_eval]
    simpa [eval_add,hl,Expr.eval,Op.eval] using coord i hi ⟨0,by decide⟩
  have ly : (formulaField front.length (literal+2)).eval (front++context input)=Encodable.encode c[i].offset.2 := by
    rw [formulaField_eval]
    simpa [eval_add,hl,Expr.eval,Op.eval] using coord i hi ⟨1,by decide⟩
  have hx : (formulaField front.length (header+2)).eval (front++context input)=Encodable.encode c[0].offset.1 := by
    rw [formulaField_eval]
    simpa [eval_add,hh,Expr.eval,Op.eval,Nat.add_assoc] using coord 0 hn ⟨0,by decide⟩
  have hy : (formulaField front.length (header+3)).eval (front++context input)=Encodable.encode c[0].offset.2 := by
    rw [formulaField_eval]
    simpa [eval_add,hh,Expr.eval,Op.eval,Nat.add_assoc] using coord 0 hn ⟨1,by decide⟩
  have anchor : PeriodicCNF.clauseAnchor c = c[0].offset := by
    cases c with
    | nil => simp at hn
    | cons l ls => rfl
  simp only [offset,pointEval,subtract_eval,fromCode_eval _ _ _ lx,fromCode_eval _ _ _ ly,
    fromCode_eval _ _ _ hx,fromCode_eval _ _ _ hy,anchor,Cell.sub]

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram
