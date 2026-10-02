/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceStripFieldTransition
import LeanTrominoes.PeriodicCNFFieldCycleSearch
import LeanTrominoes.PeriodicCNFFieldBudgetPolynomial
import LeanTrominoes.PartrecFlatFieldPolySpace
import LeanTrominoes.PolyominoStripSearchSetup

/-! # A complete Savitch evaluator for arbitrary strip footprint records

The transition program is specialized to the native records above. The
countdown, fixed-width adapters, and cycle search reuse the same verified
space accounting as the local CNF solver.
-/
namespace LeanTrominoes.PeriodicSubspaceTiling.Strip.FieldSavitch

set_option maxHeartbeats 200000
open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState

/-- The saved footprint context has zero placeholders for the two changing words. -/
def suffix (f : Input) : List Nat := FieldPredicate.input f 0 0

def restoreInputCode : Code :=
  Code.prepend ((Code.get 0).comp DivideEvalPartrec.flatContextCode)
    (Code.prepend ((Code.get 1).comp DivideEvalPartrec.flatContextCode)
      (Code.prepend ((Code.get 2).comp DivideEvalPartrec.flatContextCode)
        (Code.prepend (Code.get 5) (Code.prepend (Code.get 6)
          ((Code.drop 5).comp DivideEvalPartrec.flatContextCode)))))

def restoreCoefficient : Nat :=
  4*(projectCoefficient 0+4*(projectCoefficient 1+4*(projectCoefficient 2+
    4*(60000+4*(70000+projectCoefficient 5+1)+1)+1)+1)+1)

theorem restoreInput_eval (f : Input) (context count : Nat) (state : DivideEvalState) :
    restoreInputCode.eval (divideEvalProgramList context count state ++ suffix f) =
      pure (FieldPredicate.input f state.query.first state.query.last) := by
  have ctx := DivideEvalPartrec.flatContextCode_eval context count state (suffix f)
  simp only [restoreInputCode,Code.prepend_eval_eq,Code.eval,ctx,Part.bind_eq_bind,Part.bind_some]
  simp [suffix,FieldPredicate.input,FieldPredicate.context,divideEvalProgramList,DivideEvalState.toNatList]

theorem restoreInput_fits (f : Input) (context count : Nat) (state : DivideEvalState) :
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



open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

theorem decision_code_eval (f : Input) (a b : Nat) :
    FieldPredicate.decision.code.eval (FieldPredicate.input f a b) = pure [(FieldPredicate.check f a b).toNat] := by
  rw [Expr.code_eval,FieldPredicate.decision_eval]

/-- A path of length at most one also permits equal endpoints. -/
def decisionCoefficient : Nat := FieldPredicate.decision.weight*(FieldPredicate.decision.radius+1)

theorem decision_code_fits (f : Input) (a b : Nat) :
    EvaluatorCodeFits FieldPredicate.decision.code (FieldPredicate.input f a b) [(FieldPredicate.check f a b).toNat]
      (decisionCoefficient*(encodedListSpace (FieldPredicate.input f a b)+1)) := by
  have fit := FieldPredicate.decision.code_fits_automatic (FieldPredicate.input f a b) FieldPredicate.decision_noPower
  rw [FieldPredicate.decision_eval] at fit
  exact fit

def baseExpr : Expr := .ite (eqE (var 3) (var 4)) 1 FieldPredicate.decision

def baseCode : Code := baseExpr.code.comp restoreInputCode

def baseExprCoefficient : Nat := baseExpr.weight*(baseExpr.radius+1)
def baseCoefficient : Nat := baseExprCoefficient*(restoreCoefficient+1)+restoreCoefficient

def baseCost (f : Input) (context count : Nat) (state : DivideEvalState) : Nat :=
  baseCoefficient*(encodedListSpace (GenericSavitchStep.flatProgramList (suffix f) context count state)+1)

theorem baseExpr_noPower : baseExpr.noPower = true := by
  simp [baseExpr,eqE,Expr.noPower,FieldPredicate.decision_noPower]

theorem baseExpr_eval (f : Input) (first last : Nat) :
    baseExpr.eval (FieldPredicate.input f first last) =
      divideBoolTag (decide (first=last) || FieldPredicate.check f first last) := by
  have he : (eqE (var 3) (var 4)).eval (FieldPredicate.input f first last) =
      if first=last then 1 else 0 := rfl
  change (if (eqE (var 3) (var 4)).eval (FieldPredicate.input f first last) = 0 then
    FieldPredicate.decision.eval (FieldPredicate.input f first last) else 1) = _
  rw [he,FieldPredicate.decision_eval f first last]
  by_cases h : first=last
  · simp [h,divideBoolTag]
  · simp only [h,if_false,ite_true,decide_false,Bool.false_or]
    cases FieldPredicate.check f first last <;> rfl

theorem base_eval (f : Input)
    (context count : Nat) (state : DivideEvalState) :
    baseCode.eval (divideEvalProgramList context count state ++ suffix f) =
      pure [divideBoolTag (decide (state.query.first=state.query.last) ||
        FieldPredicate.check f state.query.first state.query.last)] := by
  have step : baseCode.eval (divideEvalProgramList context count state ++ suffix f) =
      baseExpr.code.eval (FieldPredicate.input f state.query.first state.query.last) := by
    simp [baseCode,restoreInput_eval,Part.bind_eq_bind]
  rw [step,Expr.code_eval,baseExpr_eval f state.query.first state.query.last]

theorem base_fits (f : Input)
    (context count : Nat) (state : DivideEvalState) :
    EvaluatorCodeFits baseCode (GenericSavitchStep.flatProgramList (suffix f) context count state)
      [divideBoolTag (decide (state.query.first=state.query.last) || FieldPredicate.check f state.query.first state.query.last)]
      (baseCost f context count state) := by
  have leaf := baseExpr.code_fits_automatic
    (FieldPredicate.input f state.query.first state.query.last) baseExpr_noPower
  rw [baseExpr_eval f state.query.first state.query.last] at leaf
  have inputFit := restoreInput_fits f context count state
  exact comp_linear leaf inputFit



open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState

def countdownBudget (bits suffixSpace : Nat) : Nat :=
  GenericSavitchReach.reachBudget (stateBudget bits suffixSpace)
    (baseCoefficient*(stateBudget bits suffixSpace+1)) (fuelBits bits)

theorem countdown_fits (f : Input) (bits first last : Nat)
    (hf : first < 2^bits) (hl : last < 2^bits) :
    EvaluatorCodeFits (Code.flatIterate (DivideEvalPartrec.stepCode baseCode))
      (divideEvalFuel (2^bits) bits :: GenericSavitchStep.flatProgramList (suffix f) 0 (2^bits)
        (divideEvalInitial bits first last))
      (GenericSavitchStep.flatProgramList (suffix f) 0 (2^bits)
        (((divideEvalStep (2^bits) (FieldPredicate.check f))^[divideEvalFuel (2^bits) bits])
          (divideEvalInitial bits first last)))
      (countdownBudget bits (encodedListSpace (suffix f))) := by
  apply GenericSavitchReach.iterate_fits (suffix f) baseCode (FieldPredicate.check f)
    (baseCost f) (base_fits f) 0 (2^bits)
    (divideEvalFuel (2^bits) bits) (divideEvalInitial bits first last)
    (stateBudget bits (encodedListSpace (suffix f)))
    (baseCoefficient*(stateBudget bits (encodedListSpace (suffix f))+1)) (fuelBits bits)
    (fuel_length_le bits)
  · intro taken ht
    exact state_space_le _ _ bits first last taken hf hl
  · intro taken ht
    have h := state_space_le (suffix f) (FieldPredicate.check f) bits first last taken hf hl
    exact Nat.mul_le_mul_left baseCoefficient (Nat.add_le_add_right h 1)



open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

def answerExpr : Expr := var 3-1
def answerCoefficient : Nat := answerExpr.weight*(answerExpr.radius+1)

def reachCode : Code := answerExpr.code.comp ((Code.flatIterate (DivideEvalPartrec.stepCode baseCode)).comp reachInputCode)

def finalState (f : Input) (bits first last : Nat) : DivideEvalState :=
  ((divideEvalStep (2^bits) (FieldPredicate.check f))^[divideEvalFuel (2^bits) bits])
    (divideEvalInitial bits first last)

theorem answer_eval (rest : List Nat) (count : Nat) (state : DivideEvalState) :
    answerExpr.eval (GenericSavitchStep.flatProgramList rest 0 count state) =
      divideBoolTag (state.answer.getD false) := by
  change (divideOptionBoolTag state.answer)-1 = _
  cases state.answer with
  | none => rfl
  | some answer => cases answer <;> rfl

theorem reach_eval (f : Input) (bits first last : Nat) :
    reachCode.eval (reachRequest bits first last (suffix f)) =
      pure [divideBoolTag (divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits first last)] := by
  have inputRun := reachInput_eval bits first last (suffix f)
  have loopRun := DivideEvalPartrec.flatIterate_stepCode_eval_suffix baseCode 0 (2^bits)
    (FieldPredicate.check f) (suffix f)
    (base_eval f 0 (2^bits))
    (divideEvalFuel (2^bits) bits) (divideEvalInitial bits first last)
  have step : reachCode.eval (reachRequest bits first last (suffix f)) =
      answerExpr.code.eval (GenericSavitchStep.flatProgramList (suffix f) 0 (2^bits)
        (finalState f bits first last)) := by
    simp [reachCode,inputRun,GenericSavitchStep.flatProgramList,loopRun,Part.bind_eq_bind,finalState]
  rw [step,Expr.code_eval,answer_eval]
  rfl

def requestBudget (bits suffixSpace : Nat) : Nat := 4*(bits+2)+suffixSpace

theorem request_space_le (bits first last : Nat) (rest : List Nat) (hf : first < 2^bits) (hl : last < 2^bits) :
    encodedListSpace (reachRequest bits first last rest) ≤ requestBudget bits (encodedListSpace rest) := by
  have countBits : (Computability.encodeNat (2^bits)).length ≤ bits+1 :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ (Nat.pow_lt_pow_right (by omega) (by omega))
  have depthBits : (Computability.encodeNat bits).length ≤ bits+1 :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ (bits.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
  have firstBits := FiniteState.encodeNat_length_le_of_lt_pow first bits hf
  have lastBits := FiniteState.encodeNat_length_le_of_lt_pow last bits hl
  simp [reachRequest,requestBudget,encodedListSpace_cons]
  omega

def reachBudget (bits suffixSpace : Nat) : Nat :=
  answerCoefficient*(stateBudget bits suffixSpace+1)+countdownBudget bits suffixSpace+
    reachInputCoefficient*(requestBudget bits suffixSpace+fuelBits bits+1)

theorem reach_fits (f : Input) (bits first last : Nat)
    (hf : first < 2^bits) (hl : last < 2^bits) :
    EvaluatorCodeFits reachCode (reachRequest bits first last (suffix f))
      [divideBoolTag (divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits first last)]
      (reachBudget bits (encodedListSpace (suffix f))) := by
  let rest := suffix f
  let final := GenericSavitchStep.flatProgramList rest 0 (2^bits) (finalState f bits first last)
  have initial := reachInput_fits bits first last rest
  have loop := countdown_fits f bits first last hf hl
  have answer := answerExpr.code_fits_automatic final (by simp [answerExpr,Expr.noPower])
  have eq : answerExpr.eval final = divideBoolTag (divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits first last) :=
    answer_eval rest (2^bits) (finalState f bits first last)
  rw [eq] at answer
  have result := comp answer (comp loop initial)
  apply result.mono
  have hs := state_space_le rest (FieldPredicate.check f) bits first last (divideEvalFuel (2^bits) bits) hf hl
  have hi := request_space_le bits first last rest hf hl
  change encodedListSpace final ≤ stateBudget bits (encodedListSpace rest) at hs
  change answerCoefficient*(encodedListSpace final+1)+(countdownBudget bits (encodedListSpace rest)+
    reachInputCoefficient*reachInputUnit bits first last rest) ≤ reachBudget bits (encodedListSpace rest)
  unfold reachBudget reachInputUnit
  have hm := Nat.mul_le_mul_left answerCoefficient (Nat.add_le_add_right hs 1)
  have hn := Nat.mul_le_mul_left reachInputCoefficient (Nat.add_le_add_right hi (fuelBits bits+1))
  nlinarith



open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState

def pairValues (bits first second : Nat) (rest : List Nat) : List Nat := [second,first,2^bits,bits] ++ rest

def pairReachInputCode : Code := Code.prepend (Code.get 2) (Code.prepend (Code.get 3)
  (Code.prepend (Code.get 0) (Code.prepend (Code.get 1) (Code.drop 4))))

def pairTransitionInputCode : Code := Code.prepend (Code.get 4) (Code.prepend (Code.get 5)
  (Code.prepend (Code.get 6) (Code.prepend (Code.get 1) (Code.prepend (Code.get 0) (Code.drop 9)))))

def pairReachCoefficient : Nat := 4*(30000+4*(40000+4*(10000+4*(20000+50000+1)+1)+1)+1)
def pairTransitionCoefficient : Nat := 4*(50000+4*(60000+4*(70000+4*(20000+4*(10000+100000+1)+1)+1)+1)+1)

theorem pairReachInput_eval (bits first second : Nat) (rest : List Nat) :
    pairReachInputCode.eval (pairValues bits first second rest) = pure (reachRequest bits second first rest) := by
  simp [pairReachInputCode,pairValues,reachRequest]

theorem pairTransitionInput_eval (f : Input) (bits first second : Nat) :
    pairTransitionInputCode.eval (pairValues bits first second (suffix f)) =
      pure (FieldPredicate.input f first second) := by
  simp [pairTransitionInputCode,pairValues,suffix,FieldPredicate.input,FieldPredicate.context]

theorem pairReachInput_fits (bits first second : Nat) (rest : List Nat) :
    EvaluatorCodeFits pairReachInputCode (pairValues bits first second rest) (reachRequest bits second first rest)
      (pairReachCoefficient*(encodedListSpace (pairValues bits first second rest)+1)) := by
  let values := pairValues bits first second rest
  have fit := prepend_linear (get_linear 2 values) (prepend_linear (get_linear 3 values)
    (prepend_linear (get_linear 0 values) (prepend_linear (get_linear 1 values) (drop_linear 4 values))))
  change EvaluatorCodeFits pairReachInputCode values (reachRequest bits second first rest)
    (pairReachCoefficient*(encodedListSpace values+1)) at fit
  exact fit

theorem pairTransitionInput_fits (f : Input) (bits first second : Nat) :
    EvaluatorCodeFits pairTransitionInputCode (pairValues bits first second (suffix f))
      (FieldPredicate.input f first second)
      (pairTransitionCoefficient*(encodedListSpace (pairValues bits first second (suffix f))+1)) := by
  let values := pairValues bits first second (suffix f)
  have fit := prepend_linear (get_linear 4 values) (prepend_linear (get_linear 5 values)
    (prepend_linear (get_linear 6 values) (prepend_linear (get_linear 1 values)
      (prepend_linear (get_linear 0 values) (drop_linear 9 values)))))
  change EvaluatorCodeFits pairTransitionInputCode values (FieldPredicate.input f first second)
    (pairTransitionCoefficient*(encodedListSpace values+1)) at fit
  exact fit

theorem pair_space_le (bits first second : Nat) (rest : List Nat)
    (hf : first ≤ 2^bits) (hs : second ≤ 2^bits) :
    encodedListSpace (pairValues bits first second rest) ≤ requestBudget bits (encodedListSpace rest) := by
  have power : 2^bits < 2^(bits+1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have c := FiniteState.encodeNat_length_le_of_lt_pow _ _ power
  have f := FiniteState.encodeNat_length_le_of_lt_pow _ _ (hf.trans_lt power)
  have s := FiniteState.encodeNat_length_le_of_lt_pow _ _ (hs.trans_lt power)
  have d := FiniteState.encodeNat_length_le_of_lt_pow _ _ (bits.lt_two_pow_self.trans power)
  simp [pairValues,requestBudget,encodedListSpace_cons]
  omega



open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

def pairGuard : Expr := andE (ltE (var 1) (var 2)) (ltE (var 0) (var 2))
def pairGuardCoefficient : Nat := pairGuard.weight*(pairGuard.radius+1)
def pairTransitionCode : Code := FieldPredicate.decision.code.comp pairTransitionInputCode
def pairReachCode : Code := reachCode.comp pairReachInputCode
def pairBodyCode : Code := Code.boolAnd pairTransitionCode pairReachCode
def pairCode : Code := Code.branchZero pairGuard.code Code.zero pairBodyCode

def pairTransitionTotalCoefficient : Nat :=
  decisionCoefficient*(pairTransitionCoefficient+1)+pairTransitionCoefficient

def pairPredicate (f : Input) (bits first second : Nat) : Bool :=
  decide (first < 2^bits ∧ second < 2^bits) &&
    (FieldPredicate.check f first second &&
      divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits second first)

theorem pairGuard_eval (bits first second : Nat) (rest : List Nat) :
    pairGuard.eval (pairValues bits first second rest) =
      (decide (first < 2^bits ∧ second < 2^bits)).toNat := by
  by_cases hf : first < 2^bits <;> by_cases hs : second < 2^bits <;>
    simp [pairGuard,andE,ltE,Expr.eval,Op.eval,var,pairValues,hf,hs]

theorem pairGuard_noPower : pairGuard.noPower = true := by simp [pairGuard,andE,ltE,Expr.noPower]

theorem pairTransition_eval (f : Input) (bits first second : Nat) :
    pairTransitionCode.eval (pairValues bits first second (suffix f)) =
      pure [(FieldPredicate.check f first second).toNat] := by
  simp [pairTransitionCode,pairTransitionInput_eval,Part.bind_eq_bind,
    decision_code_eval f first second]

theorem pairReach_eval (f : Input) (bits first second : Nat) :
    pairReachCode.eval (pairValues bits first second (suffix f)) =
      pure [(divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits second first).toNat] := by
  have tag (b : Bool) : divideBoolTag b = b.toNat := by cases b <;> rfl
  simp [pairReachCode,pairReachInput_eval,Part.bind_eq_bind,reach_eval f bits second first,tag]

theorem pair_eval (f : Input) (bits first second : Nat) :
    pairCode.eval (pairValues bits first second (suffix f)) =
      pure [(pairPredicate f bits first second).toNat] := by
  let values := pairValues bits first second (suffix f)
  let a := FieldPredicate.check f first second
  let b := divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits second first
  have edge := pairTransition_eval f bits first second
  have path := pairReach_eval f bits first second
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

theorem pair_fits (f : Input) (bits first second : Nat)
    (hf : first ≤ 2^bits) (hs : second ≤ 2^bits) :
    EvaluatorCodeFits pairCode (pairValues bits first second (suffix f))
      [(pairPredicate f bits first second).toNat]
      (pairBudget bits (encodedListSpace (suffix f))) := by
  let values := pairValues bits first second (suffix f)
  let space := encodedListSpace (suffix f)
  have hv := pair_space_le bits first second (suffix f) hf hs
  change encodedListSpace values ≤ requestBudget bits space at hv
  have guard := pairGuard.code_fits_automatic values pairGuard_noPower
  rw [pairGuard_eval] at guard
  have guard' : EvaluatorCodeFits pairGuard.code values
      [(decide (first < 2^bits ∧ second < 2^bits)).toNat]
      (pairGuardCoefficient*(requestBudget bits space+1)) :=
    guard.mono (Nat.mul_le_mul_left pairGuardCoefficient (Nat.add_le_add_right hv 1))
  have body : decide (first < 2^bits ∧ second < 2^bits) = true →
      EvaluatorCodeFits pairBodyCode values
        [(FieldPredicate.check f first second &&
          divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits second first).toNat]
        (pairBodyBudget bits space) := by
    intro hg
    have hg' := of_decide_eq_true hg
    have edge := comp_linear (decision_code_fits f first second)
      (pairTransitionInput_fits f bits first second)
    have edge' : EvaluatorCodeFits pairTransitionCode values [(FieldPredicate.check f first second).toNat]
        (pairTransitionTotalCoefficient*(requestBudget bits space+1)) :=
      edge.mono (Nat.mul_le_mul_left pairTransitionTotalCoefficient (Nat.add_le_add_right hv 1))
    have path := comp (reach_fits f bits second first hg'.2 hg'.1)
      (pairReachInput_fits bits first second (suffix f))
    have tag (b : Bool) : divideBoolTag b = b.toNat := by cases b <;> rfl
    simp only [tag] at path
    have path' : EvaluatorCodeFits pairReachCode values
        [(divideReachIndexDFSBool (2^bits) (FieldPredicate.check f) bits second first).toNat]
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



open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic

def cycleValues (bits : Nat) (rest : List Nat) : List Nat := [2^bits,bits] ++ rest

def outerValues (bits first : Nat) (rest : List Nat) : List Nat := first :: cycleValues bits rest

def prependFieldCode (index : Nat) : Code := Code.prepend (Code.get index) Code.id
def prependFieldCoefficient (index : Nat) : Nat := 4*(10000*(index+1)+10+1)

def outerCode : Code := (Code.boundedAnyCode pairCode).comp (prependFieldCode 1)
def cycleCode : Code := (Code.boundedAnyCode outerCode).comp (prependFieldCode 0)

def outerPredicate (f : Input) (bits first : Nat) : Bool :=
  boundedAny (pairPredicate f bits first) (2^bits)

def cyclePredicate (f : Input) (bits : Nat) : Bool :=
  boundedAny (outerPredicate f bits) (2^bits)

theorem prependField_fits (index : Nat) (values : List Nat) :
    EvaluatorCodeFits (prependFieldCode index) values ((values[index]?.getD 0) :: values)
      (prependFieldCoefficient index*(encodedListSpace values+1)) := by
  have identity := (EvaluatorCodeFits.id values).mono (idCost_bound values)
  exact prepend_linear (get_linear index values) identity

theorem outer_space_le (bits first : Nat) (rest : List Nat) (hf : first ≤ 2^bits) :
    encodedListSpace (outerValues bits first rest) ≤ requestBudget bits (encodedListSpace rest) := by
  have h := pair_space_le bits first 0 rest hf (by omega)
  change encodedListSpace (0 :: outerValues bits first rest) ≤ _ at h
  simp only [encodedListSpace_cons] at h
  omega

theorem cycle_space_le (bits : Nat) (rest : List Nat) :
    encodedListSpace (cycleValues bits rest) ≤ requestBudget bits (encodedListSpace rest) := by
  have h := outer_space_le bits 0 rest (Nat.zero_le _)
  change encodedListSpace (0 :: cycleValues bits rest) ≤ _ at h
  simp only [encodedListSpace_cons] at h
  omega

theorem counter_length_le (bits : Nat) : (Computability.encodeNat (2^bits)).length ≤ bits+1 :=
  FiniteState.encodeNat_length_le_of_lt_pow _ _ (Nat.pow_lt_pow_right (by omega) (by omega))

theorem outer_eval (f : Input) (bits first : Nat) :
    outerCode.eval (outerValues bits first (suffix f)) =
      pure [(outerPredicate f bits first).toNat] := by
  have run := Code.boundedAnyCode_eval pairCode (outerValues bits first (suffix f))
    (pairPredicate f bits first)
    (fun second => pair_eval f bits first second) (2^bits)
  have prep : (prependFieldCode 1).eval (outerValues bits first (suffix f)) =
      pure (2^bits :: outerValues bits first (suffix f)) := by
    simp [prependFieldCode,outerValues,cycleValues]
  simpa [outerCode,prep,outerPredicate,Part.bind_eq_bind] using run

theorem cycle_eval_guarded (f : Input) (bits : Nat) :
    cycleCode.eval (cycleValues bits (suffix f)) =
      pure [(cyclePredicate f bits).toNat] := by
  have run := Code.boundedAnyCode_eval outerCode (cycleValues bits (suffix f))
    (outerPredicate f bits) (fun first => outer_eval f bits first) (2^bits)
  have prep : (prependFieldCode 0).eval (cycleValues bits (suffix f)) =
      pure (2^bits :: cycleValues bits (suffix f)) := by simp [prependFieldCode,cycleValues]
  simpa [cycleCode,prep,cyclePredicate,Part.bind_eq_bind] using run

private theorem boundedAny_congr (p q : Nat → Bool) (count : Nat) (h : ∀ i < count, p i = q i) :
    boundedAny p count = boundedAny q count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [boundedAny,boundedAny,h n (by omega),ih (fun i hi => h i (by omega))]

theorem cyclePredicate_eq (f : Input) (bits : Nat) :
    cyclePredicate f bits = cycleSearchIndexDFSBoolAtDepth (2^bits) bits (FieldPredicate.check f) := by
  unfold cyclePredicate outerPredicate cycleSearchIndexDFSBoolAtDepth
  apply boundedAny_congr
  intro first hf
  apply boundedAny_congr
  intro second hs
  simp [pairPredicate,hf,hs]

theorem cycle_eval (f : Input) (bits : Nat) :
    cycleCode.eval (cycleValues bits (suffix f)) =
      pure [(cycleSearchIndexDFSBoolAtDepth (2^bits) bits (FieldPredicate.check f)).toNat] := by
  rw [cycle_eval_guarded f bits,cyclePredicate_eq]

def innerAnyBudget (bits space : Nat) : Nat := boundedAnyBudget (requestBudget bits space) (bits+1) (pairBudget bits space)
def outerBudget (bits space : Nat) : Nat := innerAnyBudget bits space+prependFieldCoefficient 1*(requestBudget bits space+1)
def outerAnyBudget (bits space : Nat) : Nat := boundedAnyBudget (requestBudget bits space) (bits+1) (outerBudget bits space)
def cycleBudget (bits space : Nat) : Nat := outerAnyBudget bits space+prependFieldCoefficient 0*(requestBudget bits space+1)

theorem outer_fits (f : Input) (bits first : Nat)
    (hf : first ≤ 2^bits) :
    EvaluatorCodeFits outerCode (outerValues bits first (suffix f))
      [(outerPredicate f bits first).toNat]
      (outerBudget bits (encodedListSpace (suffix f))) := by
  let values := outerValues bits first (suffix f)
  let space := encodedListSpace (suffix f)
  have hv : encodedListSpace values ≤ requestBudget bits space := outer_space_le bits first _ hf
  have inner := boundedAny_uniform pairCode values (pairPredicate f bits first)
    (2^bits) (bits+1) (pairBudget bits space) (counter_length_le bits)
    (fun second hs => pair_fits f bits first second hf hs)
  have inner' : EvaluatorCodeFits (Code.boundedAnyCode pairCode) (2^bits :: values)
      [(outerPredicate f bits first).toNat] (innerAnyBudget bits space) := by
    apply inner.mono
    unfold innerAnyBudget boundedAnyBudget
    omega
  have prep := prependField_fits 1 values
  have prep' : EvaluatorCodeFits (prependFieldCode 1) values (2^bits :: values)
      (prependFieldCoefficient 1*(requestBudget bits space+1)) :=
    prep.mono (Nat.mul_le_mul_left _ (Nat.add_le_add_right hv 1))
  exact comp inner' prep'

theorem cycle_fits (f : Input) (bits : Nat) :
    EvaluatorCodeFits cycleCode (cycleValues bits (suffix f))
      [(cycleSearchIndexDFSBoolAtDepth (2^bits) bits (FieldPredicate.check f)).toNat]
      (cycleBudget bits (encodedListSpace (suffix f))) := by
  let values := cycleValues bits (suffix f)
  let space := encodedListSpace (suffix f)
  have hv : encodedListSpace values ≤ requestBudget bits space := cycle_space_le bits _
  have outer := boundedAny_uniform outerCode values (outerPredicate f bits)
    (2^bits) (bits+1) (outerBudget bits space) (counter_length_le bits)
    (fun first hf => outer_fits f bits first hf)
  have outer' : EvaluatorCodeFits (Code.boundedAnyCode outerCode) (2^bits :: values)
      [(cyclePredicate f bits).toNat] (outerAnyBudget bits space) := by
    apply outer.mono
    unfold outerAnyBudget boundedAnyBudget
    omega
  have prep := prependField_fits 0 values
  have prep' : EvaluatorCodeFits (prependFieldCode 0) values (2^bits :: values)
      (prependFieldCoefficient 0*(requestBudget bits space+1)) :=
    prep.mono (Nat.mul_le_mul_left _ (Nat.add_le_add_right hv 1))
  have fit := comp outer' prep'
  rw [cyclePredicate_eq] at fit
  exact fit



open PolyominoStripWindow.Savitch
open Turing.PartrecToTM2.EvaluatorCodeFits
open Polynomial

noncomputable def anyBudgetPolynomial (space bits leaf : Polynomial Nat) : Polynomial Nat :=
  1000*(10000000*(space+bits+1000*(leaf+4)+1)+4)

noncomputable def cycleBudgetPolynomial (bits space : Polynomial Nat) : Polynomial Nat :=
  let request := 4*(bits+2)+space
  let dfs := 3*(bits+2)+bits*(4*(bits+2)+5)+3+2*bits+5+space
  let fuel := (bits+1)*(bits+3)+1
  let countdown := 100000*(C 1000000000000000000000000000000*(dfs+C baseCoefficient*(dfs+1)+1)+fuel+1)
  let reach := C answerCoefficient*(dfs+1)+countdown+C reachInputCoefficient*(request+fuel+1)
  let pairBody := 1000*(request+C pairTransitionTotalCoefficient*(request+1)+(reach+C pairReachCoefficient*(request+1))+2)
  let pair := C pairGuardCoefficient*(request+1)+pairBody+10000*(request+1)+100*(request+2)
  let inner := anyBudgetPolynomial request (bits+1) pair
  let outer := inner+C (prependFieldCoefficient 1)*(request+1)
  anyBudgetPolynomial request (bits+1) outer+C (prependFieldCoefficient 0)*(request+1)

theorem cycleBudgetPolynomial_eval (bits space : Polynomial Nat) (length : Nat) :
    (cycleBudgetPolynomial bits space).eval length = cycleBudget (bits.eval length) (space.eval length) := by
  simp only [cycleBudgetPolynomial,anyBudgetPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_ofNat,cycleBudget,outerAnyBudget,outerBudget,innerAnyBudget,
    boundedAnyBudget,pairBudget,guardBudget,pairBodyBudget,reachBudget,countdownBudget,
    FiniteState.GenericSavitchReach.reachBudget,iterationBudget,stateBudget,requestBudget,fuelBits]

theorem cycleBudget_mono {bits bits' space space' : Nat} (hb : bits ≤ bits') (hs : space ≤ space') :
    cycleBudget bits space ≤ cycleBudget bits' space' := by
  unfold cycleBudget outerAnyBudget outerBudget innerAnyBudget boundedAnyBudget pairBudget guardBudget
    pairBodyBudget reachBudget countdownBudget FiniteState.GenericSavitchReach.reachBudget iterationBudget
    stateBudget requestBudget fuelBits
  gcongr



open PolyominoStripWindow.Savitch
open PeriodicCNFFlatEncoding
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

def bits (f : Input) : Nat := Strip.bits f.2.1 f.1

def result (f : Input) : Bool :=
  cycleSearchIndexDFSBoolAtDepth (2^bits f) (bits f) (FieldPredicate.check f)

theorem result_correct (f : Input) : result f = true ↔ Problem f := by
  rw [result,cycleSearchIndexDFSBoolAtDepth_eq]
  exact (cycleSearchIndexBoolAtDepth_eq_true_iff (2^bits f) (bits f) (FieldPredicate.check f) le_rfl).trans
    (FieldPredicate.cycle_iff f)

def bitsExpr : Expr := var 0*(2*var 1+1)
def bitsCoefficient : Nat := bitsExpr.weight*(bitsExpr.radius+1)
def countCode : Code := Code.powerTwoCode.comp bitsExpr.code

def searchInputCode : Code := Code.prepend countCode (Code.prepend bitsExpr.code Code.id)
def searchInputCoefficient : Nat := 4*(arithmeticScale+bitsCoefficient+4*(bitsCoefficient+10+1)+1)

def searchCode : Code := cycleCode.comp searchInputCode

def searchBudget (f : Input) (space : Nat) : Nat :=
  cycleBudget (bits f) space+
    searchInputCoefficient*(space+bits f+2)

theorem bits_eval (f : Input) :
    bitsExpr.eval (suffix f) = bits f := by
  change f.2.1.2.length*(2*f.1+1) = (2*f.1+1)*f.2.1.2.length
  exact Nat.mul_comm _ _

theorem bits_noPower : bitsExpr.noPower = true := by simp [bitsExpr,Expr.noPower]

theorem count_eval (f : Input) :
    countCode.eval (suffix f) = pure [2^bits f] := by
  simp [countCode,Expr.code_eval,bits_eval,Part.bind_eq_bind]

theorem searchInput_eval (f : Input) :
    searchInputCode.eval (suffix f) =
      pure (cycleValues (bits f) (suffix f)) := by
  simp [searchInputCode,count_eval,Expr.code_eval,bits_eval,cycleValues]

theorem search_eval (f : Input)  :
    searchCode.eval (suffix f) = pure [(result f).toNat] := by
  have run := cycle_eval f (bits f)
  simpa [searchCode,searchInput_eval,Part.bind_eq_bind,result] using run

theorem searchInput_fits (f : Input) :
    EvaluatorCodeFits searchInputCode (suffix f)
      (cycleValues (bits f) (suffix f))
      (searchInputCoefficient*(encodedListSpace (suffix f)+bits f+2)) := by
  let values := suffix f
  let bits := bits f
  let unit := encodedListSpace values+bits+2
  have hu : encodedListSpace values+1 ≤ unit := by omega
  have bitFit := bitsExpr.code_fits_automatic values bits_noPower
  rw [bits_eval] at bitFit
  have bitFit' : EvaluatorCodeFits bitsExpr.code values [bits] (bitsCoefficient*unit) :=
    bitFit.mono (Nat.mul_le_mul_left bitsCoefficient hu)
  have pow := (powerTwo_scalar_fits bits).mono (Nat.mul_le_mul_left arithmeticScale (show bits+2 ≤ unit by omega))
  have count := comp pow bitFit'
  have count' : EvaluatorCodeFits countCode values [2^bits] ((arithmeticScale+bitsCoefficient)*unit) := by
    have eq := Nat.add_mul arithmeticScale bitsCoefficient unit
    rw [← eq] at count
    exact count
  have identity := (EvaluatorCodeFits.id values).mono ((idCost_bound values).trans (Nat.mul_le_mul_left 10 hu))
  have result := prepend_unit hu count' (prepend_unit hu bitFit' identity)
  exact result

theorem search_fits (f : Input)  :
    EvaluatorCodeFits searchCode (suffix f) [(result f).toNat]
      (searchBudget f (encodedListSpace (suffix f))) := by
  exact comp (cycle_fits f (bits f)) (searchInput_fits f)


end LeanTrominoes.PeriodicSubspaceTiling.Strip.FieldSavitch
