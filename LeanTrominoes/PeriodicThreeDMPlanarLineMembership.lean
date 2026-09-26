/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMDrawingVerifier
import LeanTrominoes.PeriodicThreeDMPlanarLineDecision
import LeanTrominoes.PeriodicThreeDMLineMembership
import LeanTrominoes.NativeScalarFieldPairEvaluator

/-! # Native PSPACE membership of supplied-drawing local planar 1D 3DM -/
noncomputable section
namespace LeanTrominoes.PeriodicThreeDM.NativePlanarLine
open Gadget NormalizationCompiler FlatEncoding
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open NativeScalar.FieldPair
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def code : Code := NativeScalar.FieldPair.code DrawingVerifier.program NativeLine.code

def result (input : Input) : Bool := NativeScalar.FieldPair.result DrawingVerifier.program
  (PeriodicGridDrawing.Arithmetic.fields input.drawing) (FlatEncoding.fields input.problem) (NativeLine.result input.problem)

theorem result_correct (input : Input) : result input=true ↔ LocalPlanarLineProblem input := by
  rw [result,NativeScalar.FieldPair.result,Bool.and_eq_true,decide_eq_true_eq,NativeLine.result_correct]
  change (DrawingVerifier.program.value (Planar.fields input) ≠ 0 ∧ LocalLineProblem input.problem) ↔ _
  constructor
  · rintro ⟨drawing,problem⟩
    exact ⟨problem,(DrawingVerifier.program_correct input problem.1).mp drawing⟩
  · rintro ⟨problem,drawing⟩
    exact ⟨(DrawingVerifier.program_correct input problem.1).mpr drawing,problem⟩

theorem code_eval (input : Input) : code.eval (Planar.fields input)=pure [(result input).toNat] :=
  NativeScalar.FieldPair.code_eval DrawingVerifier.program NativeLine.code
    (PeriodicGridDrawing.Arithmetic.fields input.drawing) (FlatEncoding.fields input.problem)
    (NativeLine.result input.problem) (NativeLine.code_eval input.problem)

def space : Polynomial Nat := NativeScalar.FieldPair.space DrawingVerifier.program NativeLine.space

theorem fields_space (input : Input) : encodedListSpace (Planar.fields input)=(Planar.finEncoding.encode input).length := by
  change encodedListSpace (Planar.fields input)=(PeriodicCNFFlatEncoding.encodeNatFields (Planar.fields input)).length
  rw [PeriodicCNFFlatEncoding.encodeNatFields_length,encodedListSpace_eq_sum]

theorem problem_space_le (input : Input) : (FlatEncoding.finEncoding.encode input.problem).length ≤
    encodedListSpace (Planar.fields input) := by
  rw [← FieldSavitch.fields_space]
  have h := dynamicDropSpace_drop_le (PeriodicGridDrawing.Arithmetic.fields input.drawing).length
    (PeriodicGridDrawing.Arithmetic.fields input.drawing++FlatEncoding.fields input.problem)
  rw [List.drop_left] at h
  have tail := listCodeEncodedListSpace_tail_le (Planar.fields input)
  exact h.trans tail

theorem code_fits (input : Input) :
    EvaluatorCodeFits code (Planar.fields input) [(result input).toNat]
      (space.eval (Planar.finEncoding.encode input).length) := by
  have body := (NativeLine.code_fits input.problem).mono
    (polynomial_mono NativeLine.space (problem_space_le input))
  have fit := NativeScalar.FieldPair.code_fits DrawingVerifier.program NativeLine.code
    (PeriodicGridDrawing.Arithmetic.fields input.drawing) (FlatEncoding.fields input.problem)
    (NativeLine.result input.problem) NativeLine.space body
  change EvaluatorCodeFits code (Planar.fields input) [(result input).toNat]
    (space.eval (encodedListSpace (Planar.fields input))) at fit
  rwa [fields_space] at fit

def decider : Complexity.DeciderInPolySpace Planar.finEncoding LocalPlanarLineProblem :=
  deciderInPolySpace_of_flatEvaluatorRunFits Planar.fields Planar.decodeFields Planar.decodeFields_fields code result result_correct
    (fun input => by rw [code_eval]; apply Part.mem_some_iff.mpr; cases result input <;> rfl)
    space (fun input => by
      let fit := code_fits input
      let after := EvaluatorExecutionFits.ret_halt fit.output_space
      apply EvaluatorRunFits.of_call
      exact fit.call .halt _ (by simp [Planar.finEncoding,continuationSpace,trContStack]) after)

end LeanTrominoes.PeriodicThreeDM.NativePlanarLine
namespace LeanTrominoes.PeriodicThreeDM

theorem localPlanarLineProblem_inPSPACE : Complexity.InPSPACE FlatEncoding.Planar.finEncoding LocalPlanarLineProblem :=
  ⟨NativePlanarLine.decider⟩

end LeanTrominoes.PeriodicThreeDM
end
