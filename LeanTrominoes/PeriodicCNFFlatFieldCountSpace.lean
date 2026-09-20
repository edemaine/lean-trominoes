/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFlatFieldCount

/-! # Linear evaluator space for computing the flat field count -/
set_option maxHeartbeats 300000

namespace LeanTrominoes.PeriodicCNF.FlatScanner
open Turing Turing.ToPartrec Turing.PartrecToTM2
open BoundedArithmetic BoundedArithmetic.Expr PeriodicCNFFlatEncoding
open Turing.PartrecToTM2.EvaluatorCodeFits

def exprCost (e : Expr) : Nat := e.weight*(e.radius+1)
def countStepWeight : Nat := 4*(exprCost (var 0+1+4*var 1)+
  (1000000*(4*(exprCost (2+4*var 1)+10+1)+1)+4*(exprCost (2+4*var 1)+10+1))+1)

theorem countStepCode_fits (v : List Nat) :
    EvaluatorCodeFits countStepCode v (countStep v) (countStepWeight*(encodedListSpace v+1)) := by
  have hid : EvaluatorCodeFits Code.id v v (10*(encodedListSpace v+1)) := by
    apply (EvaluatorCodeFits.id v).mono
    have hz : (Computability.encodeNat 0).length = 0 := rfl
    simp [idCost,tailCost,zeroPrimeCost,hz]
    omega
  have args := prepend_linear ((2+4*var 1 : Expr).code_fits_automatic v rfl) hid
  have drop := (dynamicDrop (2+4*v[1]?.getD 0) v).mono (dynamicDropCost_le_linear _ _)
  simp only [eval_var,Expr.eval,Op.eval] at args
  have rest := comp_linear drop args
  have result := prepend_linear ((var 0+1+4*var 1 : Expr).code_fits_automatic v rfl) rest
  exact result

private theorem space_append (a b : List Nat) :
    encodedListSpace (a++b) = encodedListSpace a+encodedListSpace b := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

theorem count_state_space (f : PeriodicCNF Nat) (n : Nat) (hn : n ≤ f.clauses.length) :
    encodedListSpace ((countStep^[n]) (1 :: f.clauses.flatMap clauseFields)) ≤
      2*encodedListSpace (formulaFields f)+2 := by
  rw [countStep_partial _ _ _ hn,encodedListSpace_cons]
  have split : (f.clauses.take n).flatMap clauseFields ++ (f.clauses.drop n).flatMap clauseFields =
      f.clauses.flatMap clauseFields := by rw [← List.flatMap_append,List.take_append_drop]
  have lengths := congrArg List.length split
  rw [List.length_append] at lengths
  have spaces := congrArg encodedListSpace split
  rw [space_append] at spaces
  have b := encodeNat_length_le_self (1+((f.clauses.take n).flatMap clauseFields).length)
  have len := list_length_le_encodedListSpace (f.clauses.flatMap clauseFields)
  simp only [formulaFields,encodedListSpace_cons]
  omega

theorem count_iteration_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits (Code.flatIterate countStepCode)
      (f.clauses.length :: 1 :: f.clauses.flatMap clauseFields)
      [(formulaFields f).length]
      (iterationBudget (3*countStepWeight*(encodedListSpace (formulaFields f)+1))
        (encodedListSpace (formulaFields f))) := by
  have counter : (Computability.encodeNat f.clauses.length).length ≤ encodedListSpace (formulaFields f) := by
    simp only [formulaFields,encodedListSpace_cons]
    omega
  have run := flatIterate_uniform countStepCode countStep (1 :: f.clauses.flatMap clauseFields)
    f.clauses.length (3*countStepWeight*(encodedListSpace (formulaFields f)+1))
    (encodedListSpace (formulaFields f)) counter (by
      intro n hn
      rw [Function.iterate_succ_apply']
      apply (countStepCode_fits _).mono
      have bound := count_state_space f n hn
      nlinarith [Nat.mul_le_mul_left countStepWeight bound])
  simpa [countStep_iterate,formulaFields,Nat.add_comm] using run

private theorem one_linear (v : List Nat) :
    EvaluatorCodeFits Code.one v [1] (10000*(encodedListSpace v+1)) := by
  apply (EvaluatorCodeFits.one v).mono
  have headSpace := listCodeEncodedListSpace_singleton_headI_le v
  have headBits : (Computability.encodeNat v.headI).length ≤ encodedListSpace v := by
    simpa [encodedListSpace_cons] using headSpace
  have hs := listCodeEncodeNat_succ_length_le v.headI
  simp only [Nat.succ_eq_add_one] at hs
  have hz : (Computability.encodeNat 0).length = 0 := rfl
  have ho : (Computability.encodeNat 1).length = 1 := rfl
  simp [oneCost,zeroCost,nilCost,zeroPrimeCost,tailCost,succCost,hz,ho]
  omega

def headerWeight : Nat → Nat
  | 0 => 20000
  | n+1 => 4*(10000+headerWeight n+1)

def fieldCountWeight := headerWeight 2+100000*(3*countStepWeight+2)

theorem fieldCountCode_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits fieldCountCode (formulaFields f) [(formulaFields f).length]
      (fieldCountWeight*(encodedListSpace (formulaFields f)+1)) := by
  have input := prepend_linear (get_linear 0 (formulaFields f))
    (prepend_linear (one_linear (formulaFields f)) (drop_linear 1 (formulaFields f)))
  have input' : EvaluatorCodeFits fieldCountInputCode (formulaFields f)
      (f.clauses.length :: 1 :: f.clauses.flatMap clauseFields)
      (headerWeight 2*(encodedListSpace (formulaFields f)+1)) := by
    simpa only [fieldCountInputCode,headerWeight,formulaFields,List.getElem?_cons_zero,
      Option.getD_some,List.drop_succ_cons,List.drop_zero] using input
  apply (EvaluatorCodeFits.comp (count_iteration_fits f) input').mono
  unfold iterationBudget fieldCountWeight
  nlinarith

def scanInputWeight := 4*(fieldCountWeight+headerWeight 5+1)
def scannerWeight := scanInputWeight+100000*(1000*stepWeight+2)

/-- The complete preprocessor takes only the original flat encoding, and uses
linear evaluator space to return its field count and both position masks. -/
theorem scannerCode_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits scannerCode (formulaFields f)
      [(formulaFields f).length,0,0,clauseMarks 1 f.clauses,literalMarks 1 f.clauses]
      (scannerWeight*((finEncoding.encode f).length+1)) := by
  let v := formulaFields f
  have z := zero_unit v (encodedListSpace v+1) le_rfl
  have init := prepend_linear (one_linear v) (prepend_linear z
    (prepend_linear (get_linear 0 v) (prepend_linear z (prepend_linear z (drop_linear 1 v)))))
  have input := prepend_linear (fieldCountCode_fits f) init
  have input' : EvaluatorCodeFits scanInputCode v
      ((formulaFields f).length :: (initial f).fields)
      (scanInputWeight*(encodedListSpace v+1)) := by
    simpa only [scanInputCode,scanInputWeight,headerWeight,v,initial,State.fields,State.pending,
      formulaFields,List.flatMap_nil,List.nil_append,List.cons_append,List.nil_append,
      List.length_nil,List.getElem?_cons_zero,Option.getD_some,List.drop_succ_cons,List.drop_zero]
      using input
  have run := EvaluatorCodeFits.comp (scanCode_fits f) input'
  have final : (scan f).fields =
      [(formulaFields f).length,0,0,clauseMarks 1 f.clauses,literalMarks 1 f.clauses] := by
    simp [State.fields,State.pending,(scan_finished f).1,(scan_finished f).2,
      scan_cursor,(scan_masks f).1,(scan_masks f).2]
  rw [final] at run
  apply run.mono
  have enc : (finEncoding.encode f).length = encodedListSpace (formulaFields f) := by
    rw [finEncoding_encode_length,encodedListSpace_eq_sum]
  rw [enc]
  dsimp only [scannerWeight,iterationBudget,v]
  nlinarith

end LeanTrominoes.PeriodicCNF.FlatScanner
