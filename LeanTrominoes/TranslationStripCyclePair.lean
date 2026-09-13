/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripCyclePair
import LeanTrominoes.TranslationStripReach

/-! # Orientation-restricted strip CyclePair certificates

The input adapters and relation-independent bounds reuse the existing strip solver.
-/

namespace LeanTrominoes.TranslationStrip.Savitch
open PolyominoStripWindow PolyominoStripWindow.Savitch

open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

def pairTransitionCode : Code := TranslationStrip.Formula.transitionDecision.code.comp pairTransitionInputCode
def pairReachCode : Code := reachCode.comp pairReachInputCode
def pairBodyCode : Code := Code.boolAnd pairTransitionCode pairReachCode
def pairCode : Code := Code.branchZero pairGuard.code Code.zero pairBodyCode

def pairTransitionTotalCoefficient : Nat :=
  TranslationStrip.Formula.transitionSpaceConstant*(pairTransitionCoefficient+1)+pairTransitionCoefficient

def pairPredicate (cells : Bool → List Cell) (height bound bits first second : Nat) : Bool :=
  decide (first < 2^bits ∧ second < 2^bits) &&
    (TranslationStrip.check cells height bound first second &&
      divideReachIndexDFSBool (2^bits) (TranslationStrip.check cells height bound) bits second first)

theorem pairTransition_eval (cells : Bool → List Cell) (height bound bits first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    pairTransitionCode.eval (pairValues bits first second (suffix cells height bound)) =
      pure [(TranslationStrip.check cells height bound first second).toNat] := by
  simp [pairTransitionCode,pairTransitionInput_eval,Part.bind_eq_bind,
    TranslationStrip.Formula.transition_code_eval cells height bound first second bounded]

theorem pairReach_eval (cells : Bool → List Cell) (height bound bits first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    pairReachCode.eval (pairValues bits first second (suffix cells height bound)) =
      pure [(divideReachIndexDFSBool (2^bits) (TranslationStrip.check cells height bound) bits second first).toNat] := by
  have tag (b : Bool) : divideBoolTag b = b.toNat := by cases b <;> rfl
  simp [pairReachCode,pairReachInput_eval,Part.bind_eq_bind,reach_eval cells height bound bits second first bounded,tag]

theorem pair_eval (cells : Bool → List Cell) (height bound bits first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    pairCode.eval (pairValues bits first second (suffix cells height bound)) =
      pure [(pairPredicate cells height bound bits first second).toNat] := by
  let values := pairValues bits first second (suffix cells height bound)
  let a := TranslationStrip.check cells height bound first second
  let b := divideReachIndexDFSBool (2^bits) (TranslationStrip.check cells height bound) bits second first
  have edge := pairTransition_eval cells height bound bits first second bounded
  have path := pairReach_eval cells height bound bits first second bounded
  have inner := Code.boolAnd_eval_at pairTransitionCode pairReachCode values a.toNat b.toNat edge path
  have inner' : pairBodyCode.eval values = pure [(a && b).toNat] := by
    cases ha : a <;> cases hb : b <;> simpa [pairBodyCode,ha,hb] using inner
  have guard : pairGuard.code.eval values = pure [(decide (first < 2^bits ∧ second < 2^bits)).toNat] := by
    rw [Expr.code_eval,pairGuard_eval]
  by_cases hg : first < 2^bits ∧ second < 2^bits
  · have h := Code.branchZero_eval_succ_at pairGuard.code Code.zero pairBodyCode values 1
      (by simpa [hg] using guard) [(a && b).toNat] inner' (by decide)
    simpa [pairCode,pairPredicate,hg,a,b,values] using h
  · have h := Code.branchZero_eval_zero_at pairGuard.code Code.zero pairBodyCode values 0
      (by simpa [hg] using guard) [0] (by simp) rfl
    simpa [pairCode,pairPredicate,hg,a,b,values] using h

def pairBodyBudget (bits space : Nat) : Nat :=
  1000*(requestBudget bits space+pairTransitionTotalCoefficient*(requestBudget bits space+1)+
    (reachBudget bits space+pairReachCoefficient*(requestBudget bits space+1))+2)

def pairBudget (bits space : Nat) : Nat :=
  guardBudget (requestBudget bits space) (pairGuardCoefficient*(requestBudget bits space+1)) (pairBodyBudget bits space)

theorem pair_fits (cells : Bool → List Cell) (height bound bits first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (hf : first ≤ 2^bits) (hs : second ≤ 2^bits) :
    EvaluatorCodeFits pairCode (pairValues bits first second (suffix cells height bound))
      [(pairPredicate cells height bound bits first second).toNat]
      (pairBudget bits (encodedListSpace (suffix cells height bound))) := by
  let values := pairValues bits first second (suffix cells height bound)
  let space := encodedListSpace (suffix cells height bound)
  have hv := pair_space_le bits first second (suffix cells height bound) hf hs
  change encodedListSpace values ≤ requestBudget bits space at hv
  have guard := pairGuard.code_fits_automatic values pairGuard_noPower
  rw [pairGuard_eval] at guard
  have guard' : EvaluatorCodeFits pairGuard.code values
      [(decide (first < 2^bits ∧ second < 2^bits)).toNat]
      (pairGuardCoefficient*(requestBudget bits space+1)) :=
    guard.mono (Nat.mul_le_mul_left pairGuardCoefficient (Nat.add_le_add_right hv 1))
  have body : decide (first < 2^bits ∧ second < 2^bits) = true →
      EvaluatorCodeFits pairBodyCode values
        [(TranslationStrip.check cells height bound first second &&
          divideReachIndexDFSBool (2^bits) (TranslationStrip.check cells height bound) bits second first).toNat]
        (pairBodyBudget bits space) := by
    intro hg
    have hg' := of_decide_eq_true hg
    have edge := comp_linear (TranslationStrip.Formula.transition_code_fits cells height bound first second bounded)
      (pairTransitionInput_fits cells height bound bits first second)
    have edge' : EvaluatorCodeFits pairTransitionCode values [(TranslationStrip.check cells height bound first second).toNat]
        (pairTransitionTotalCoefficient*(requestBudget bits space+1)) :=
      edge.mono (Nat.mul_le_mul_left pairTransitionTotalCoefficient (Nat.add_le_add_right hv 1))
    have path := comp (reach_fits cells height bound bits second first bounded hg'.2 hg'.1)
      (pairReachInput_fits bits first second (suffix cells height bound))
    have tag (b : Bool) : divideBoolTag b = b.toNat := by cases b <;> rfl
    simp only [tag] at path
    have path' : EvaluatorCodeFits pairReachCode values
        [(divideReachIndexDFSBool (2^bits) (TranslationStrip.check cells height bound) bits second first).toNat]
        (reachBudget bits space+pairReachCoefficient*(requestBudget bits space+1)) := by
      apply path.mono
      exact Nat.add_le_add_left (Nat.mul_le_mul_left pairReachCoefficient (Nat.add_le_add_right hv 1)) _
    have both := boolAnd_bool edge' path'
    apply both.mono
    unfold pairBodyBudget
    exact Nat.mul_le_mul_left 1000 (by omega)
  have fit := guard_bool guard' body
  apply fit.mono
  change guardBudget (encodedListSpace values) (pairGuardCoefficient*(requestBudget bits space+1))
    (pairBodyBudget bits space) ≤ pairBudget bits space
  unfold pairBudget guardBudget
  omega

end LeanTrominoes.TranslationStrip.Savitch
