/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMRouteProgram
import LeanTrominoes.PeriodicThreeDMDrawingCounts
import LeanTrominoes.PeriodicThreeDMDrawingGeometry
import LeanTrominoes.PeriodicThreeDMDrawingVerifierSemantics

/-! # A linear-space verifier for native supplied 3DM drawings -/
namespace LeanTrominoes.PeriodicThreeDM.DrawingVerifier
open Gadget NormalizationCompiler PeriodicGridDrawing BoundedArithmetic NativeScalar

def routeProgram : Program := conjunction (RouteProgram.oneColor .red)
  (conjunction (RouteProgram.oneColor .green) (RouteProgram.oneColor .blue))

theorem routes_correct (input : Input) (wf : input.problem.IsWellFormed)
    (vertices : input.drawing.vertexPositions.length=input.problem.incidenceGraph.vertices.length)
    (routes : input.drawing.edgeRoutes.length=input.problem.incidenceGraph.edges.length) :
    routeProgram.value (FlatEncoding.Planar.fields input) ≠ 0 ↔
      FiniteDrawingCertificate.routesMatchCheck input.problem input.drawing=true := by
  simp only [routeProgram,conjunction_truth,RouteProgram.oneColor_truth input wf vertices routes]
  rw [routesMatchCheck_iff_indexed input.problem input.drawing wf]
  constructor
  · rintro ⟨r,g,b⟩ i hi color
    cases color with
    | red => exact r i hi
    | green => exact g i hi
    | blue => exact b i hi
  · intro h
    exact ⟨fun i hi => h i hi .red,fun i hi => h i hi .green,fun i hi => h i hi .blue⟩

def program : Program := conjunction (arithmetic DrawingCounts.predicate DrawingCounts.noPower)
  (conjunction DrawingGeometry.program routeProgram)

theorem program_correct (input : Input) (wf : input.problem.IsWellFormed) :
    program.value (FlatEncoding.Planar.fields input) ≠ 0 ↔
      FiniteDrawingCertificate.verifies input.problem input.drawing=true := by
  simp only [program,conjunction_truth]
  change DrawingCounts.predicate.Truth (FlatEncoding.Planar.fields input) ∧ _ ↔ _
  rw [DrawingCounts.correct,DrawingGeometry.program_correct,
    FiniteDrawingCertificate.verifies_iff_finiteContacts _ _ wf]
  by_cases counts : input.drawing.vertexPositions.length=input.problem.incidenceGraph.vertices.length ∧
      input.drawing.edgeRoutes.length=input.problem.incidenceGraph.edges.length
  · rw [routes_correct input wf counts.1 counts.2]
    simp only [DrawingGeometry.Valid,FiniteDrawingCertificate.compatibleCheck,
      Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,
      FiniteDrawingCertificate.positionInFundamentalSquareCheck,PositionInFundamentalSquare]
    tauto
  · simp only [DrawingGeometry.Valid,FiniteDrawingCertificate.compatibleCheck,
      Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,
      FiniteDrawingCertificate.positionInFundamentalSquareCheck,PositionInFundamentalSquare]
    tauto

def result (input : Input) : Bool := decide (program.value (FlatEncoding.Planar.fields input) ≠ 0)
def code := (normalize program).code

theorem code_eval (input : Input) : code.eval (FlatEncoding.Planar.fields input) = pure [(result input).toNat] := by
  rw [code,(normalize program).evaluates,normalize_value]
  rfl

theorem result_correct (input : Input) (wf : input.problem.IsWellFormed) :
    result input=true ↔ FiniteDrawingCertificate.verifies input.problem input.drawing=true := by
  simp only [result,decide_eq_true_eq]
  exact program_correct input wf

end LeanTrominoes.PeriodicThreeDM.DrawingVerifier
