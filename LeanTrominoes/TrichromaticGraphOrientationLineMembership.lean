/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFieldEvaluator
import LeanTrominoes.TrichromaticGraphOrientationCoreGuard
import LeanTrominoes.TrichromaticGraphOrientationVertexGuard
import LeanTrominoes.PartrecFlatFieldPolySpace
import LeanTrominoes.PartrecBooleanUniformSpace

/-! # Native binary PSPACE membership of local one-dimensional colored graph orientation -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.NativeLine
open FlatEncoding BoundedArithmetic BoundedArithmetic.Expr
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits Polynomial

def guard : Expr := andE CoreGuard.core VertexGuard.guard
def decision : Expr := .ite guard 1 0
def metadata (graph : Input) : Bool := decide (guard.eval (FieldPredicate.input graph 0 0) ≠ 0)

theorem metadata_correct (graph : Input) : metadata graph = true ↔
    IsWellFormed graph ∧ IsOneDimensional graph ∧ IsLocal graph := by
  simp only [metadata,decide_eq_true_eq]
  change guard.Truth (FieldPredicate.input graph 0 0) ↔ _
  rw [guard,truth_and,CoreGuard.core_truth,VertexGuard.guard_truth]
  unfold IsWellFormed
  tauto

theorem decision_eval (graph : Input) :
    decision.eval (FieldPredicate.input graph 0 0) = (metadata graph).toNat := by
  by_cases zero : guard.eval (FieldPredicate.input graph 0 0)=0 <;>
    simp [decision,Expr.eval,metadata,zero]

theorem decision_noPower : decision.noPower = true := by
  simp [decision,guard,andE,Expr.noPower,CoreGuard.core_noPower,VertexGuard.guard_noPower]

def decisionCoefficient : Nat := decision.weight*(decision.radius+1)
def coefficient : Nat := 6*decisionCoefficient+FieldSavitch.suffixCoefficient
def metadataCode : Code := decision.code.comp FieldSavitch.suffixCode

theorem metadataCode_eval (graph : Input) : metadataCode.eval (fields graph) = pure [(metadata graph).toNat] := by
  simp [metadataCode,FieldSavitch.suffixCode_eval,Part.bind_eq_bind,Expr.code_eval,
    FieldSavitch.suffix,decision_eval]

theorem metadata_fits (graph : Input) :
    EvaluatorCodeFits metadataCode (fields graph) [(metadata graph).toNat]
      (coefficient*((finEncoding.encode graph).length+1)) := by
  have checker := decision.code_fits_automatic (FieldPredicate.input graph 0 0) decision_noPower
  rw [decision_eval] at checker
  have fit := comp checker (FieldSavitch.suffixCode_fits graph)
  apply fit.mono
  have bound := FieldSavitch.suffix_space graph
  change encodedListSpace (FieldPredicate.input graph 0 0) ≤ 2*(finEncoding.encode graph).length+5 at bound
  change decisionCoefficient*(encodedListSpace (FieldPredicate.input graph 0 0)+1)+
    FieldSavitch.suffixCoefficient*((finEncoding.encode graph).length+1) ≤ _
  calc
    _ ≤ decisionCoefficient*(6*((finEncoding.encode graph).length+1))+
        FieldSavitch.suffixCoefficient*((finEncoding.encode graph).length+1) := by
      gcongr; omega
    _ = coefficient*((finEncoding.encode graph).length+1) := by unfold coefficient; ring

def code : Code := Code.boolAnd metadataCode FieldSavitch.decideCode
def result (graph : Input) : Bool := metadata graph && FieldSavitch.result graph
def space : Polynomial Nat := 1000*(X+C coefficient*(X+1)+FieldSavitch.spacePolynomial+2)

theorem result_correct (graph : Input) : result graph = true ↔ LocalLineProblem graph := by
  rw [result,Bool.and_eq_true,metadata_correct]
  constructor
  · rintro ⟨⟨wf,horizontal,locality⟩,oriented⟩
    exact ⟨⟨locality,wf,(FieldSavitch.result_correct graph horizontal locality).mp oriented⟩,horizontal⟩
  · rintro ⟨⟨locality,wf,oriented⟩,horizontal⟩
    exact ⟨⟨wf,horizontal,locality⟩,(FieldSavitch.result_correct graph horizontal locality).mpr oriented⟩

theorem code_eval (graph : Input) : code.eval (fields graph) = pure [(result graph).toNat] := by
  have run := Code.boolAnd_eval_at metadataCode FieldSavitch.decideCode (fields graph)
    (metadata graph).toNat (FieldSavitch.result graph).toNat (metadataCode_eval graph) (FieldSavitch.decide_eval graph)
  cases first : metadata graph <;> cases second : FieldSavitch.result graph <;>
    simpa [code,result,first,second] using run

theorem code_fits (graph : Input) :
    EvaluatorCodeFits code (fields graph) [(result graph).toNat] (space.eval (finEncoding.encode graph).length) := by
  have fit := boolAnd_bool (metadata_fits graph) (FieldSavitch.decide_fits graph)
  rw [FieldSavitch.fields_space] at fit
  simpa only [code,result,space,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] using fit

def decider : Complexity.DeciderInPolySpace finEncoding LocalLineProblem :=
  deciderInPolySpace_of_flatEvaluatorRunFits fields decodeFields decodeFields_fields code result result_correct
    (fun graph => by rw [code_eval]; apply Part.mem_some_iff.mpr; cases result graph <;> rfl)
    space (fun graph => by
      let fit := code_fits graph
      let after := EvaluatorExecutionFits.ret_halt fit.output_space
      apply EvaluatorRunFits.of_call
      exact fit.call .halt _ (by simp [finEncoding,continuationSpace,trContStack]) after)

end LeanTrominoes.TrichromaticGraphOrientation.NativeLine
namespace LeanTrominoes.TrichromaticGraphOrientation

theorem localLineProblem_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding LocalLineProblem :=
  ⟨NativeLine.decider⟩

end LeanTrominoes.TrichromaticGraphOrientation
end
