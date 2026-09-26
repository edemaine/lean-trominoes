/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnarySegmentFieldsProjection
import LeanTrominoes.UnaryFieldClosure

/-! # Polynomial-time counts and exact finite-check radius for drawing headers -/
noncomputable section
namespace LeanTrominoes.PeriodicGridDrawing.NativeCompiler
open Computability Turing UnaryColumn
open UnaryFieldEncoderMachine (unaryFields)

private theorem code_abs (z : Int) : (Encodable.encode z + 1) / 2 = z.natAbs := by
  cases z with
  | ofNat n => change (2*n+1)/2 = n; omega
  | negSucc n => change (2*n+1+1)/2 = n+1; omega

private def coordinates (points : List Cell) : List Int := points.flatMap (fun p => [p.1,p.2])

private theorem coordinate_codes (points : List Cell) :
    points.flatMap Arithmetic.pointFields = (coordinates points).map Encodable.encode := by
  simp only [coordinates, List.map_flatMap, List.map_cons, List.map_nil]
  rfl

private theorem coordinate_abs_sum (points : List Cell) :
    ((coordinates points).map Int.natAbs).sum = (points.map (fun p => p.1.natAbs + p.2.natAbs)).sum := by
  induction points with
  | nil => rfl
  | cons p points ih =>
      simp only [coordinates, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil] at ih ⊢
      omega

variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]

def pointRadiusCompiler (points : List Symbol → List Cell)
    (source : TM2ComputableInPolyTime id unaryFields (fun s => (points s).flatMap Arithmetic.pointFields)) :
    ScalarCompiler (fun s => ((points s).map (fun p => p.1.natAbs+p.2.natAbs)).sum) := by
  have codes : Compiler (fun s => coordinates (points s)) (fun _ z => Encodable.encode z) :=
    TM2ComputableInPolyTime.of_eq source (fun s => coordinate_codes _)
  let absolute := halve (add codes (constant codes 1))
  have absCompiler : Compiler (fun s => coordinates (points s)) (fun _ z => z.natAbs) :=
    TM2ComputableInPolyTime.of_eq absolute (fun s => List.map_congr_left (fun z _ => code_abs z))
  let physical := TM2CompositionMachine.computableInPolyTime absCompiler UnaryFieldAggregate.sumCompiler
  exact TM2ComputableInPolyTime.of_eq physical (fun s => congrArg List.singleton (coordinate_abs_sum _))

private theorem pointFieldCount (points : List Cell) :
    (points.flatMap Arithmetic.pointFields).length = 2 * points.length := by
  induction points with
  | nil => rfl
  | cons p points ih => simp [Arithmetic.pointFields, ih]; omega

def vertexCountCompiler (drawing : List Symbol → PeriodicGridDrawing)
    (vertices : TM2ComputableInPolyTime id unaryFields
      (fun s => (drawing s).vertexPositions.flatMap Arithmetic.pointFields)) :
    ScalarCompiler (fun s => (drawing s).vertexPositions.length) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime vertices UnaryFieldAggregate.countCompiler)
    UnaryFieldHalve.computableInPolyTime
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [List.map_cons, List.map_nil, pointFieldCount]
  congr 1
  omega

def radiusCompiler (drawing : List Symbol → PeriodicGridDrawing)
    (vertices : TM2ComputableInPolyTime id unaryFields
      (fun s => (drawing s).vertexPositions.flatMap Arithmetic.pointFields))
    (segments : TM2ComputableInPolyTime id unaryFields
      (fun s => (drawing s).indexedSegments.flatMap Arithmetic.segmentFields)) :
    ScalarCompiler (fun s => FiniteBounds.radius (drawing s)) := by
  let endpoints := UnarySegmentFieldsProjection.compiler (fun s => (drawing s).indexedSegments) true segments
  let physical := UnaryFieldClosure.appendCompiler id _ _ vertices endpoints
  have points : TM2ComputableInPolyTime id unaryFields
      (fun s => (FiniteBounds.points (drawing s)).flatMap Arithmetic.pointFields) := by
    apply TM2ComputableInPolyTime.of_eq physical
    intro s
    simp only [FiniteBounds.points, List.flatMap_append, List.flatMap_assoc,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  exact pointRadiusCompiler (fun s => FiniteBounds.points (drawing s)) points

end LeanTrominoes.PeriodicGridDrawing.NativeCompiler
end
