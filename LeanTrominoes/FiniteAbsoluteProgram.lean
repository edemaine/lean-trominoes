/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteAbsoluteExpression
import LeanTrominoes.PeriodicCNFTransitionProgram

/-! # Absolute-time postorder programs for the finite CNF backend -/
namespace LeanTrominoes.FiniteCNF
open PeriodicCNF

def absoluteInstruction (time : Nat) : TransitionInstruction → TransitionInstruction
  | .wire wire => .wire (absoluteWire time wire)
  | instruction => instruction

theorem absoluteExpression_program (time : Nat) (expression : TransitionExpr) :
    (absoluteExpression time expression).program=
      expression.program.map (absoluteInstruction time) := by
  induction expression <;> simp_all [absoluteExpression,TransitionExpr.program,absoluteInstruction]

theorem absoluteExpression_atCurrent (time : Nat) (expression : TransitionExpr) :
    (absoluteExpression time expression).atCurrent=absoluteExpression time expression := by
  induction expression <;> simp_all [absoluteExpression,TransitionExpr.atCurrent,absoluteWire]

theorem all_program (expressions : List TransitionExpr) :
    (TransitionExpr.all expressions).program=
      expressions.flatMap TransitionExpr.program++[.constant true]++
        List.replicate expressions.length .conjoin := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
    simp [TransitionExpr.all,TransitionExpr.program,ih,List.replicate_succ,
      List.append_assoc]
    rw [← List.replicate_succ',List.replicate_succ]

theorem tableauExpression_program (expressions : Nat → TransitionExpr) (steps : Nat) :
    (tableauExpression expressions steps).program=
      (List.range steps).flatMap (fun time =>
        (expressions time).program.map (absoluteInstruction time))++
        [.constant true]++List.replicate steps .conjoin := by
  simp [tableauExpression,all_program,absoluteExpression_program,List.flatMap_map]

theorem tableauExpression_atCurrent (expressions : Nat → TransitionExpr) (steps : Nat) :
    (tableauExpression expressions steps).atCurrent=tableauExpression expressions steps := by
  have h (es : List TransitionExpr) (current : ∀ e∈es, e.atCurrent=e) :
      (TransitionExpr.all es).atCurrent=TransitionExpr.all es := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      simp only [TransitionExpr.all,TransitionExpr.atCurrent]
      rw [current e (by simp),ih (fun e he => current e (by simp [he]))]
  apply h
  intro e he
  obtain ⟨time,_,rfl⟩ := List.mem_map.mp he
  exact absoluteExpression_atCurrent _ _

end LeanTrominoes.FiniteCNF
