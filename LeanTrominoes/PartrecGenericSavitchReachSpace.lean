/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecGenericSavitchStepSpace
import LeanTrominoes.PartrecFlatIterationUniformSpace

/-! # Uniform workspace for an arbitrary flat-context Savitch run -/

namespace LeanTrominoes.FiniteState.GenericSavitchReach
open Turing Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits GenericSavitchStep

def programStep (suffix : List Nat) (relation : Nat → Nat → Bool) (context count : Nat)
    (values : List Nat) : List Nat :=
  let stateFields := values.take (7+6*values[2]?.getD 0)
  let state := DivideEvalState.ofNatList (stateFields.drop 3)
  flatProgramList suffix context count (divideEvalStep count relation state)

@[simp] theorem programStep_programList (suffix : List Nat) (relation : Nat → Nat → Bool)
    (context count : Nat) (state : DivideEvalState) :
    programStep suffix relation context count (flatProgramList suffix context count state) =
      flatProgramList suffix context count (divideEvalStep count relation state) := by
  have prefixLength := divideEvalProgramList_length context count state
  have takePrefix : (divideEvalProgramList context count state ++ suffix).take
      (7+6*state.stack.length) = divideEvalProgramList context count state := by
    rw [← prefixLength]
    simp
  have fieldTwo : (divideEvalProgramList context count state ++ suffix)[2]?.getD 0 = state.stack.length := by
    simp [divideEvalProgramList]
  change programStep suffix relation context count (divideEvalProgramList context count state ++ suffix) = _
  simp only [programStep]
  rw [fieldTwo,takePrefix]
  simp [divideEvalProgramList]

theorem programStep_iterate (suffix : List Nat) (relation : Nat → Nat → Bool)
    (context count steps : Nat) (state : DivideEvalState) :
    ((programStep suffix relation context count)^[steps]) (flatProgramList suffix context count state) =
      flatProgramList suffix context count (((divideEvalStep count relation)^[steps]) state) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih,programStep_programList]

def reachBudget (stateBudget leafBudget counterBits : Nat) : Nat :=
  iterationBudget (1000000000000000000000000000000*(stateBudget+leafBudget+1)) counterBits

/-- The number of iterations contributes only its binary counter length. -/
theorem iterate_fits (suffix : List Nat) (baseCode : ToPartrec.Code) (relation : Nat → Nat → Bool)
    (baseCost : Nat → Nat → DivideEvalState → Nat)
    (baseFit : ∀ context count state,
      EvaluatorCodeFits baseCode (flatProgramList suffix context count state)
        [divideBoolTag (decide (state.query.first = state.query.last) || relation state.query.first state.query.last)]
        (baseCost context count state))
    (context count fuel : Nat) (initial : DivideEvalState) (stateBudget leafBudget counterBits : Nat)
    (fuelBits : (Computability.encodeNat fuel).length ≤ counterBits)
    (stateSpace : ∀ taken ≤ fuel, encodedListSpace
      (flatProgramList suffix context count (((divideEvalStep count relation)^[taken]) initial)) ≤ stateBudget)
    (leafSpace : ∀ taken ≤ fuel,
      baseCost context count (((divideEvalStep count relation)^[taken]) initial) ≤ leafBudget) :
    EvaluatorCodeFits (ToPartrec.Code.flatIterate (DivideEvalPartrec.stepCode baseCode))
      (fuel :: flatProgramList suffix context count initial)
      (flatProgramList suffix context count (((divideEvalStep count relation)^[fuel]) initial))
      (reachBudget stateBudget leafBudget counterBits) := by
  have fit := flatIterate_uniform (DivideEvalPartrec.stepCode baseCode)
    (programStep suffix relation context count) (flatProgramList suffix context count initial)
    fuel (1000000000000000000000000000000*(stateBudget+leafBudget+1)) counterBits fuelBits
    (fun taken ht => ?_)
  · simpa only [programStep_iterate,reachBudget] using fit
  · rw [programStep_iterate,programStep_iterate,Function.iterate_succ_apply']
    apply (GenericSavitchStep.exactStep suffix baseCode relation baseCost baseFit context count _).mono
    have hs := stateSpace taken ht
    have hl := leafSpace taken ht
    unfold stepCost stepSpaceUnit
    omega

end LeanTrominoes.FiniteState.GenericSavitchReach
