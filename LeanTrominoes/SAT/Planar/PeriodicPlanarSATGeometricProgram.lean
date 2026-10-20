/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATComponentVerification
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricEndpoints
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicDrawingEndpointResidues
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicDrawingHaloGuard
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicDrawingEndpointResidueProgram
import LeanTrominoes.Computation.Compiler.NativeScalarConjunction

/-! # Space-certified geometry checks on the original supplied drawing fields -/
namespace LeanTrominoes.PeriodicPlanarSAT.GeometricProgram
open BoundedArithmetic BoundedArithmetic.Expr PeriodicGridDrawing
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits Polynomial

private def arithmetic (expr : Expr) (allowed : expr.noPower=true) := NativeScalar.arithmetic expr allowed

def orthogonalDecision : Expr := .ite (HaloGuard.orthogonal.slice 0) 1 0

theorem orthogonalDecision_noPower : orthogonalDecision.noPower=true := by
  simp only [orthogonalDecision,Expr.noPower,Expr.slice_noPower,HaloGuard.orthogonal_noPower]
  rfl

def program : NativeScalar.Program := NativeScalar.conjunction
  (arithmetic ComponentVerification.drawingDecision (by
    rw [ComponentVerification.drawingDecision,Expr.slice_noPower]
    exact Arithmetic.decision_noPower))
  (NativeScalar.conjunction (arithmetic orthogonalDecision orthogonalDecision_noPower)
    (NativeScalar.drop 1 (EndpointResidueProgram.program 0)))

theorem orthogonalDecision_truth (input : Input Nat) :
    orthogonalDecision.Truth (FlatEncoding.fields input) ↔ input.2.IsOrthogonal := by
  have eval := Expr.slice_eval HaloGuard.orthogonal []
    (FlatEncoding.drawingFields input.2) (PeriodicCNFFlatEncoding.formulaFields input.1)
  change (HaloGuard.orthogonal.slice 0).eval (FlatEncoding.fields input) =
    HaloGuard.orthogonal.eval (Arithmetic.fields input.2) at eval
  simpa [orthogonalDecision,Truth,Expr.eval,eval] using HaloGuard.orthogonal_truth input.2

theorem program_truth (input : Input Nat) :
    program.value (FlatEncoding.fields input) ≠ 0 ↔
      input.2.IsContinuouslyPlanar ∧ input.2.IsOrthogonal ∧
        ∀ first ∈ input.2.indexedRoutePoints, ∀ second ∈ input.2.indexedRoutePoints,
          EndpointResidueProgram.Contact input.2 first second := by
  rw [program,NativeScalar.conjunction_truth,NativeScalar.conjunction_truth]
  change (ComponentVerification.drawingDecision.Truth (FlatEncoding.fields input) ∧
    orthogonalDecision.Truth (FlatEncoding.fields input) ∧
    (EndpointResidueProgram.program 0).value ((FlatEncoding.fields input).drop 1) ≠ 0) ↔ _
  rw [orthogonalDecision_truth]
  have continuous : ComponentVerification.drawingDecision.Truth (FlatEncoding.fields input) ↔
      input.2.IsContinuouslyPlanar := by
    change ComponentVerification.drawingDecision.eval (FlatEncoding.fields input) ≠ 0 ↔ _
    rw [ComponentVerification.drawingDecision_eval,← FiniteBounds.check_correct]
    cases FiniteBounds.check input.2 <;> decide
  rw [continuous]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  simpa only [FlatEncoding.fields,List.drop_succ_cons,List.drop_zero,List.nil_append,List.length_nil]
    using EndpointResidueProgram.program_points input.2 [] (PeriodicCNFFlatEncoding.formulaFields input.1)

theorem contacts_iff (d : PeriodicGridDrawing) :
    (∀ first ∈ d.indexedRoutePoints, ∀ second ∈ d.indexedRoutePoints,
      EndpointResidueProgram.Contact d first second) ↔ d.EndpointResidues := by
  constructor
  · intro h first hf second hs unequal residues
    rcases h first hf second hs with same | different | endpoints
    · exact False.elim (unequal (indexedRoutePoint_eq_of_mem_of_indices_eq hf hs same.1 same.2))
    · exact False.elim (different residues)
    · exact endpoints
  · intro h first hf second hs
    by_cases same : first.routeIndex=second.routeIndex ∧ first.pointIndex=second.pointIndex
    · exact Or.inl same
    · apply Or.inr
      by_cases residues : OrbitCertificate.residue d.gridSize first.point = OrbitCertificate.residue d.gridSize second.point
      · apply Or.inr
        apply h first hf second hs _ residues
        intro equal
        exact same ⟨congrArg IndexedRoutePoint.routeIndex equal,congrArg IndexedRoutePoint.pointIndex equal⟩
      · exact Or.inl residues

theorem correct (input : Input Nat) :
    program.value (FlatEncoding.fields input) ≠ 0 ↔ StrongGeometry input.2 := by
  rw [program_truth,contacts_iff,endpointResidues_iff]
  unfold StrongGeometry IsRibbonReady
  tauto

def normalized : NativeScalar.Program := NativeScalar.normalize program

def result (input : Input Nat) : Bool := decide (program.value (FlatEncoding.fields input) ≠ 0)

theorem result_correct (input : Input Nat) : result input=true ↔ StrongGeometry input.2 := by
  simp only [result,decide_eq_true_eq,correct]

theorem normalized_value (input : Input Nat) :
    normalized.value (FlatEncoding.fields input) = (result input).toNat :=
  NativeScalar.normalize_value program _

theorem code_eval (input : Input Nat) :
    normalized.code.eval (FlatEncoding.fields input) = pure [(result input).toNat] := by
  rw [normalized.evaluates,normalized_value]

theorem code_fits (input : Input Nat) :
    EvaluatorCodeFits normalized.code (FlatEncoding.fields input) [(result input).toNat]
      (normalized.coefficient*((FlatEncoding.finEncoding.encode input).length+1)) := by
  have fit := normalized.fits (FlatEncoding.fields input)
  rw [normalized_value,FlatEncoding.fields_space] at fit
  exact fit

end LeanTrominoes.PeriodicPlanarSAT.GeometricProgram
