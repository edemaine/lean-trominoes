/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TranslationStripRaw
import LeanTrominoes.PolyominoStripTransitionExprSpace

/-! # A bounded arithmetic checker for the orientation restriction -/

namespace LeanTrominoes.TranslationStrip.Formula
open PolyominoStripWindow PolyominoStripWindow.Formula BoundedArithmetic BoundedArithmetic.Expr
open Turing.PartrecToTM2

def legalLeaf : Expr :=
  impE (eqE (var 3) 0) (impE (selected 4 false 0) (impE (eqE (var 2) 1) (eqE (var 1) 0)))

def legal : Expr := forallCandidates 0 legalLeaf

theorem legal_truth (cells : Bool → List Cell) (height bound first second : Nat) :
    legal.Truth (Arithmetic.input cells height bound first second) ↔ Legal height bound first := by
  have quant := forallCandidates_truth cells height bound first second [] legalLeaf
  simp only [List.length_nil,List.nil_append] at quant
  rw [legal,quant]
  have leaf (a : Raw.Candidate) (ha : a ∈ Raw.keys height bound) :
      legalLeaf.Truth (Arithmetic.candidateFields a ++ Arithmetic.input cells height bound first second) ↔
      (a.1 = 0 → Raw.selected height bound first a = true → Allowed a.2.1 a.2.2.1) := by
    have sf := selected_truth cells height bound first second [] a false 0
    simp only [List.length_nil,Nat.reduceAdd,List.nil_append] at sf
    rw [legalLeaf,truth_imp,truth_eq,truth_imp,sf,truth_imp,truth_eq,truth_eq]
    rw [Raw.selected_eq_testBit_address height bound first a ha]
    rcases a with ⟨column,kind,symmetry,y⟩
    cases kind <;> cases symmetry <;>
      simp [Allowed,eval_var,Arithmetic.candidateFields,Raw.symmetryIndex,Expr.eval]
  conv_lhs => intro a ha; rw [leaf a ha]
  constructor
  · intro h slot hs bit
    exact h (0,slot) ((Raw.mem_keys _).mpr ⟨by omega,(Raw.mem_slots _).mp hs⟩) rfl bit
  · intro h a ha hc bit
    have hs := (Raw.mem_slots a.2).mpr ((Raw.mem_keys a).mp ha).2
    have eq : a = (0,a.2) := Prod.ext hc rfl
    exact h a.2 hs (by rw [eq] at bit; exact bit)

theorem legal_noPower : legal.noPower = true := by
  apply forallCandidates_noPower
  simp [legalLeaf,impE,eqE,selected,address,Expr.noPower]

def transitionDecision : Expr := .ite legal PolyominoStripWindow.Formula.transitionDecision 0

theorem transitionDecision_eval (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    transitionDecision.eval (Arithmetic.input cells height bound first second) =
      (TranslationStrip.check cells height bound first second).toNat := by
  have correct := legal_truth cells height bound first second
  unfold Truth at correct
  by_cases h : legal.eval (Arithmetic.input cells height bound first second) = 0
  · have no : ¬ Legal height bound first := by simpa [h] using correct.symm
    simp [transitionDecision,Expr.eval,h,TranslationStrip.check,no]
  · have yes := correct.mp h
    simp only [transitionDecision,Expr.eval,h,if_false]
    rw [PolyominoStripWindow.Formula.transitionDecision_eval cells height bound first second bounded]
    simp [TranslationStrip.check,yes]

theorem transitionDecision_noPower : transitionDecision.noPower = true := by
  simp [transitionDecision,Expr.noPower,legal_noPower,PolyominoStripWindow.Formula.transitionDecision_noPower]

def transitionSpaceConstant : Nat := transitionDecision.weight*(transitionDecision.radius+1)

theorem transition_code_eval (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    transitionDecision.code.eval (Arithmetic.input cells height bound first second) =
      pure [(TranslationStrip.check cells height bound first second).toNat] := by
  rw [Expr.code_eval,transitionDecision_eval cells height bound first second bounded]

theorem transition_code_fits (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    EvaluatorCodeFits transitionDecision.code (Arithmetic.input cells height bound first second)
      [(TranslationStrip.check cells height bound first second).toNat]
      (transitionSpaceConstant*(encodedListSpace (Arithmetic.input cells height bound first second)+1)) := by
  have fit := transitionDecision.code_fits_automatic
    (Arithmetic.input cells height bound first second) transitionDecision_noPower
  rw [transitionDecision_eval cells height bound first second bounded] at fit
  exact fit

end LeanTrominoes.TranslationStrip.Formula
