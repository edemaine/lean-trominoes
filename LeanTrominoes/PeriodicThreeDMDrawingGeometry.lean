/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingContactSemantics
import LeanTrominoes.PeriodicDrawingHaloGuard
import LeanTrominoes.PeriodicDrawingVertexPredicate
import LeanTrominoes.PeriodicDrawingArithmeticCorrectness
import LeanTrominoes.PeriodicThreeDMFlatEncoding
import LeanTrominoes.BoundedArithmeticSlice
import LeanTrominoes.NativeScalarConjunction

/-! # Geometric checks on the native supplied-drawing input -/
namespace LeanTrominoes.PeriodicThreeDM.DrawingGeometry
open Gadget NormalizationCompiler PeriodicGridDrawing BoundedArithmetic BoundedArithmetic.Expr

def geometric : Expr := andE (VertexPredicate.predicate false)
  (andE HaloGuard.orthogonal (andE HaloGuard.halo Arithmetic.predicate))

theorem geometric_noPower : geometric.noPower=true := by decide

def program : NativeScalar.Program := NativeScalar.conjunction
  (NativeScalar.arithmetic (geometric.slice 0) (by rw [Expr.slice_noPower]; exact geometric_noPower))
  (ContactProgram.program 1)

def Valid (d : PeriodicGridDrawing) : Prop :=
  (d.vertexPositions.Nodup ∧ ∀ p ∈ d.vertexPositions, d.PositionInFundamentalSquare p) ∧
  (d.IsOrthogonal ∧ d.SegmentEndpointsInExpandedSquare ∧ d.IsContinuouslyPlanar) ∧
  d.expandedFiniteRoutePointsMeetOnlyAtEndpoints=true

set_option maxHeartbeats 2000000 in
theorem program_correct (input : Input) :
    program.value (FlatEncoding.Planar.fields input) ≠ 0 ↔ Valid input.drawing := by
  rw [program,NativeScalar.conjunction_truth]
  have slice := geometric.slice_eval [] (Arithmetic.fields input.drawing) (FlatEncoding.fields input.problem)
  have contact := ContactProgram.program_correct input.drawing [(Arithmetic.fields input.drawing).length]
    (FlatEncoding.fields input.problem)
  change (geometric.slice 0).eval (FlatEncoding.Planar.fields input)=geometric.eval (Arithmetic.fields input.drawing) at slice
  change (geometric.slice 0).eval (FlatEncoding.Planar.fields input) ≠ 0 ∧ _ ↔ _
  rw [slice]
  change geometric.Truth (Arithmetic.fields input.drawing) ∧ _ ↔ _
  rw [geometric,truth_and,truth_and,truth_and,VertexPredicate.predicate_truth,
    HaloGuard.orthogonal_truth,HaloGuard.halo_truth,Arithmetic.predicate_correct]
  change (ContactProgram.program 1).value (FlatEncoding.Planar.fields input) ≠ 0 ↔ _ at contact
  rw [contact]
  change ((_ ∧ _ ∧ _ ∧ _) ∧ _) ↔ (_ ∧ (_ ∧ _ ∧ _) ∧ _)
  simp only [VertexPredicate.Valid,Bool.false_eq_true,if_false]
  tauto

end LeanTrominoes.PeriodicThreeDM.DrawingGeometry
