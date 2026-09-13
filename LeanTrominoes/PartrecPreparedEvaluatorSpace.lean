/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TM2SequentialSpace
import LeanTrominoes.PartrecFlatFieldPolySpace

/-! # Polynomial-space evaluators after polynomial-time input preparation -/

noncomputable section
namespace Turing.PartrecToTM2
open StateTransition LeanTrominoes
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Finite evaluator run with a budget supplied independently of its input encoding. -/
def finiteRunInSpace (code : ToPartrec.Code) (values output : List Nat) (budget : Nat)
    (fits : EvaluatorRunFits code values budget) (evaluates : output ∈ code.eval values) :
    EvalsToInSpace (finiteEvaluator code).step TM2.stackSpace budget
      (initList (finiteEvaluator code) (trList values))
      (haltList (finiteEvaluator code) (trList output)) where
  toEvalsTo := finiteEvaluator_outputs evaluates
  space_le := by
    intro n c _ he
    have reaches := TM2SequentialMachine.reaches_of_iterate_eq (finiteEvaluator code).step n _ _ he
    have ambient := erase_finiteEvaluator_reaches code reaches
    have ambient' : Relation.ReflTransGen (fun a b => b ∈ TM2.step tr a) (init code values) (TM2.eraseRestrictedCfg c) := by
      convert ambient using 1
      exact (erase_finiteEvaluator_init code values).symm
    exact evaluator_reachable_space_le code values output budget fits evaluates ambient'

def evaluatorAux (code : ToPartrec.Code) : TM2ComputableAux Γ' Γ' where
  tm := finiteEvaluator code
  inputAlphabet := finiteEvaluatorInputAlphabet code
  outputAlphabet := finiteEvaluatorOutputAlphabet code

variable {α : Type} (encoding : Computability.FinEncoding α) (fields : α → List Nat)
    (prepare : Complexity.FiniteAlphabetComputableInPolyTime encoding.encode trList fields)
    (code : ToPartrec.Code)

def preparedSpacePolynomial (space : Polynomial Nat) : Polynomial Nat :=
  let first := prepare.toTM2ComputableAux
  let second := evaluatorAux code
  let middle := TM2OutputLength.outputLengthPolynomial prepare.toTM2ComputableInPolyTime
  Polynomial.X + prepare.time * Polynomial.C (TM2OutputLength.machinePushBound first.tm) +
    (middle + (Polynomial.C 4 * middle + Polynomial.C 2) *
      Polynomial.C (TM2OutputLength.machinePushBound (TM2SequentialMachine.machine first second))) + space

/-- Retain the original input-length parameter through machine composition. -/
def deciderInPolySpace_of_preparedEvaluator (language : α → Prop)
    (result : α → Bool) (correct : ∀ x, result x = true ↔ language x)
    (evaluates : ∀ x, [Encodable.encode (result x)] ∈ code.eval (fields x))
    (space : Polynomial Nat)
    (fits : ∀ x, EvaluatorRunFits code (fields x) (space.eval (encoding.encode x).length)) :
    Complexity.DeciderInPolySpace encoding language := by
  let first := prepare.toTM2ComputableAux
  let second := evaluatorAux code
  let combined := TM2SequentialMachine.machine first second
  let run := fun x => TM2SequentialMachine.compositionSpaceRun first second
    (encoding.encode x) (trList (fields x)) (trList [Encodable.encode (result x)])
    (prepare.time.eval (encoding.encode x).length) (space.eval (encoding.encode x).length)
    (prepare.outputsFun x) (by
      change EvalsToInSpace (finiteEvaluator code).step TM2.stackSpace _
        (initList (finiteEvaluator code) (List.map (finiteEvaluatorInputAlphabet code).invFun (trList (fields x))))
        (haltList (finiteEvaluator code) (List.map (finiteEvaluatorOutputAlphabet code).invFun (trList [Encodable.encode (result x)])))
      simp only [map_finiteEvaluatorInputAlphabet_symm,map_finiteEvaluatorOutputAlphabet_symm]
      exact finiteRunInSpace code (fields x) _ _ (fits x) (evaluates x))
  refine {
    tm := combined
    inputAlphabet := first.inputAlphabet
    outputAlphabet := second.outputAlphabet
    stackAlphabetFinite := ?_
    result := result
    correct := correct
    outputs := ?_
    space := preparedSpacePolynomial encoding fields prepare code space
    space_le := ?_ }
  · intro stack
    cases stack with
    | first k => exact prepare.stackAlphabetFinite k
    | bridge => change Fintype Γ'; infer_instance
    | second k => change Fintype Γ'; infer_instance
  · intro x
    exact (run x).toEvalsTo
  · intro x c reaches
    have bound := (run x).space_le_of_terminal (by rfl) reaches
    have middleBound := TM2OutputLength.output_length_le_polynomial_eval prepare.toTM2ComputableInPolyTime x
    apply bound.trans
    change _ ≤ (preparedSpacePolynomial encoding fields prepare code space).eval (encoding.encode x).length
    simp only [preparedSpacePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    gcongr

end Turing.PartrecToTM2
