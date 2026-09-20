/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFlatScannerCode
import LeanTrominoes.PeriodicCNFFlatScannerSpace
import LeanTrominoes.PartrecLinearAdaptersSpace
import LeanTrominoes.PartrecFlatIterationUniformSpace

/-! # Evaluator-space certificates for the streaming CNF scanner -/
namespace LeanTrominoes.PeriodicCNF.FlatScanner
open Turing Turing.ToPartrec Turing.PartrecToTM2
open BoundedArithmetic BoundedArithmetic.Expr
open Turing.PartrecToTM2.EvaluatorCodeFits

def outputWeight : List Expr → Nat → Nat
  | [], skip => 10000*(skip+1)
  | e :: es, skip => 4*(e.weight+outputWeight es skip+1)

theorem outputCode_fits (es : List Expr) (skip : Nat) (v : List Nat) (bits : Nat)
    (hb : 1 ≤ bits) (hs : ∀ e ∈ es, e.Safe bits v) :
    EvaluatorCodeFits (outputCode es skip) v
      (es.map (fun e => e.eval v) ++ v.drop skip)
      (outputWeight es skip*(encodedListSpace v+bits+1)) := by
  induction es with
  | nil => exact drop_unit _ _ _ (by omega)
  | cons e es ih =>
    exact prepend_unit (by omega) (e.code_fits v bits hb (hs e (by simp)))
      (ih (fun e he => hs e (by simp [he])))

private theorem safe_plain (e : Expr) (v : List Nat)
    (hn : e.noPower = true) (hr : e.radius ≤ 100) :
    e.Safe (100*(encodedListSpace v+v[0]?.getD 0+1)) v := by
  apply (e.safe_automatic v hn).mono
  nlinarith

private theorem safe_mask (i : Nat) (hi : i ≤ 4) (v : List Nat) :
    (var i+.powerTwo (var 0)).Safe (100*(encodedListSpace v+v[0]?.getD 0+1)) v := by
  let b := 100*(encodedListSpace v+v[0]?.getD 0+1)
  have si := (var i).safe_automatic v rfl
  have sz := (var 0).safe_automatic v rfl
  have ri : (var i).radius ≤ 7 := by
    simp only [var,Expr.radius]
    have h := encodeNat_length_le_self i
    omega
  have rz : (var 0).radius = 2 := rfl
  have p : (Computability.encodeNat (2^(v[0]?.getD 0))).length ≤ v[0]?.getD 0+1 := by
    apply encodeNat_length_le_of_lt_pow
    rw [pow_succ]
    have hp := Nat.two_pow_pos (v[0]?.getD 0)
    omega
  have bi := si.value_bits
  have add := encodeNat_add_length_le_sum (v[i]?.getD 0) (2^(v[0]?.getD 0))
  change (var i).Safe b v ∧ ((var 0).Safe b v ∧ _) ∧ _
  refine ⟨si.mono ?_,⟨sz.mono ?_,?_⟩,?_⟩
  · dsimp [b]; nlinarith
  · rw [rz]; dsimp [b]; omega
  · exact p.trans (by omega)
  · change (Computability.encodeNat (v[i]?.getD 0+2^(v[0]?.getD 0))).length ≤ b
    change (Computability.encodeNat (v[i]?.getD 0)).length ≤ _ at bi
    dsimp [b]
    nlinarith

private theorem branch_zero_unit {t z s : Code} {v out : List Nat} {x a b u : Nat}
    (hu : encodedListSpace v+1 ≤ u) (hx : x=0)
    (ht : EvaluatorCodeFits t v [x] (a*u))
    (hb : EvaluatorCodeFits z v out (b*u)) :
    EvaluatorCodeFits (Code.branchZero t z s) v out ((10*(a+b+1))*u) := by
  apply (branchZero_zero hx ht hb).mono
  have ho := hb.output_space
  have hi := ht.output_space
  simp only [branchZeroZeroCost,branchZeroTestCost,prependCost,idCost,tailCost,
    zeroPrimeCost,encodedListSpace_cons,encodedListSpace_nil,List.headI_cons,List.tail_cons] at *
  have hz : (Computability.encodeNat 0).length = 0 := rfl
  simp only [hz] at *
  nlinarith

private theorem branch_succ_unit {t z s : Code} {v out : List Nat} {x a b u : Nat}
    (hu : encodedListSpace v+1 ≤ u) (hx : 0<x)
    (ht : EvaluatorCodeFits t v [x] (a*u))
    (hb : EvaluatorCodeFits s v out (b*u)) :
    EvaluatorCodeFits (Code.branchZero t z s) v out ((10*(a+b+1))*u) := by
  apply (branchZero_succ hx ht hb).mono
  have ho := hb.output_space
  have hi := ht.output_space
  have hp := encodeNat_length_mono (Nat.pred_le x)
  simp only [branchZeroSuccCost,branchZeroTestCost,prependCost,idCost,tailCost,
    zeroPrimeCost,encodedListSpace_cons,encodedListSpace_nil,List.headI_cons,List.tail_cons] at *
  have hz : (Computability.encodeNat 0).length = 0 := rfl
  simp only [hz] at *
  nlinarith

def clauseWeight := outputWeight [var 0+1,var 5,var 2-1,var 3+.powerTwo (var 0),var 4] 6
def literalWeight := outputWeight [var 0+4,var 1-1,var 2,var 3,var 4+.powerTwo (var 0)] 9
def stepWeight := 10*(20000+10*(30000+10+clauseWeight+1)+literalWeight+1)

theorem stepCode_fits (v : List Nat) :
    EvaluatorCodeFits stepCode v (step v)
      (stepWeight*(encodedListSpace v+100*(encodedListSpace v+v[0]?.getD 0+1)+1)) := by
  let bits := 100*(encodedListSpace v+v[0]?.getD 0+1)
  let u := encodedListSpace v+bits+1
  have hu : encodedListSpace v+1 ≤ u := by dsimp [u]; omega
  have pos : 1 ≤ bits := by dsimp [bits]; omega
  have hc := outputCode_fits
    [var 0+1,var 5,var 2-1,var 3+.powerTwo (var 0),var 4] 6 v bits pos (by
      intro e he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl
      all_goals first | exact safe_mask _ (by decide) v | exact safe_plain _ v rfl (by decide))
  have hl := outputCode_fits
    [var 0+4,var 1-1,var 2,var 3,var 4+.powerTwo (var 0)] 9 v bits pos (by
      intro e he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl
      all_goals first | exact safe_mask _ (by decide) v | exact safe_plain _ v rfl (by decide))
  change EvaluatorCodeFits clauseCode v _ (clauseWeight*u) at hc
  change EvaluatorCodeFits literalCode v _ (literalWeight*u) at hl
  simp only [List.map_cons,List.map_nil,Expr.eval_sub,eval_var,
    Expr.eval,Op.eval] at hc hl
  by_cases h1 : v[1]?.getD 0 = 0
  · have inner : EvaluatorCodeFits (Code.branchZero (Code.get 2) Code.id clauseCode)
        v (step v) ((10*(30000+10+clauseWeight+1))*u) := by
      by_cases h2 : v[2]?.getD 0 = 0
      · have hid : EvaluatorCodeFits Code.id v v (10*u) := by
          apply (EvaluatorCodeFits.id v).mono
          have hz : (Computability.encodeNat 0).length = 0 := rfl
          simp [idCost,tailCost,zeroPrimeCost,hz]
          omega
        have h := branch_zero_unit (s := clauseCode) hu h2 (get_unit 2 v u hu) hid
        apply (show EvaluatorCodeFits _ v (step v) _ from by simpa [step,h1,h2] using h).mono
        dsimp [u]; nlinarith
      · have h := branch_succ_unit (z := Code.id) hu (Nat.pos_of_ne_zero h2) (get_unit 2 v u hu) hc
        apply (show EvaluatorCodeFits _ v (step v) _ from by simpa [step,h1,h2] using h).mono
        dsimp [u]; nlinarith
    exact (branch_zero_unit hu h1 (get_unit 1 v u hu) inner).mono (by
      change (10*(20000+10*(30000+10+clauseWeight+1)+1))*u ≤ stepWeight*u
      unfold stepWeight; nlinarith)
  · have h := branch_succ_unit (z := Code.branchZero (Code.get 2) Code.id clauseCode) hu (Nat.pos_of_ne_zero h1) (get_unit 1 v u hu) hl
    apply (show EvaluatorCodeFits stepCode v (step v) _ from by simpa [stepCode,step,h1] using h).mono
    change (10*(20000+literalWeight+1))*u ≤ stepWeight*u
    unfold stepWeight; nlinarith

/-- Every iteration has a uniform linear evaluator-space bound in the original input. -/
theorem reachable_step_fits (f : PeriodicCNF Nat) (n : Nat) :
    EvaluatorCodeFits stepCode ((step^[n]) (initial f).fields)
      ((step^[n+1]) (initial f).fields)
      ((1000*stepWeight)*(encodedListSpace (PeriodicCNFFlatEncoding.formulaFields f)+1)) := by
  rw [Function.iterate_succ_apply']
  apply (stepCode_fits _).mono
  rw [iterate_fields]
  have hs := state_space_bound f n
  have hm := (masks_bound f n).1
  have hn := list_length_le_encodedListSpace (PeriodicCNFFlatEncoding.formulaFields f)
  have hget : (((State.step^[n]) (initial f)).fields)[0]?.getD 0 =
      ((State.step^[n]) (initial f)).cursor := by simp [State.fields]
  rw [hget]
  have h : encodedListSpace ((State.step^[n]) (initial f)).fields+
      100*(encodedListSpace ((State.step^[n]) (initial f)).fields+
      ((State.step^[n]) (initial f)).cursor+1)+1 ≤
      1000*(encodedListSpace (PeriodicCNFFlatEncoding.formulaFields f)+1) := by omega
  nlinarith [Nat.mul_le_mul_left stepWeight h]

/-- A concrete countdown program scans a well-formed formula in linear evaluator space. -/
theorem scanCode_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits (Code.flatIterate stepCode)
      ((PeriodicCNFFlatEncoding.formulaFields f).length :: (initial f).fields)
      (scan f).fields
      (iterationBudget
        ((1000*stepWeight)*(encodedListSpace (PeriodicCNFFlatEncoding.formulaFields f)+1))
        (encodedListSpace (PeriodicCNFFlatEncoding.formulaFields f))) := by
  have counter := (encodeNat_length_le_self (PeriodicCNFFlatEncoding.formulaFields f).length).trans
    (list_length_le_encodedListSpace _)
  have run := flatIterate_uniform stepCode step (initial f).fields
    (PeriodicCNFFlatEncoding.formulaFields f).length _ _ counter
    (fun n _ => reachable_step_fits f n)
  simpa only [iterate_fields,scan] using run

end LeanTrominoes.PeriodicCNF.FlatScanner
