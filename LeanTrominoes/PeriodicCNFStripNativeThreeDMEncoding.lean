/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMDrawingRoutes
import LeanTrominoes.PeriodicCNFStripNativeThreeDMDrawingVertices
import LeanTrominoes.PeriodicCNFStripNativeThreeDMFields
import LeanTrominoes.PeriodicDrawingFieldsCompiler
import LeanTrominoes.PeriodicThreeDMPlanarEncodingCompiler

/-! # Complete native encoding of the periodic 3DM reduction and its drawing -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing UnaryColumn PeriodicThreeDM
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

private def assembleTrailer {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (drawing : List Symbol → PeriodicGridDrawing)
    (count : ScalarCompiler (fun s => (drawing s).edgeRoutes.length))
    (fields : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (drawing s).edgeRoutes.flatMap PeriodicGridDrawing.Arithmetic.routeFields)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => PeriodicGridDrawing.Arithmetic.trailer (drawing s)) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _ count fields
  exact TM2ComputableInPolyTime.of_eq physical (fun s => by
    simp only [PeriodicGridDrawing.Arithmetic.trailer,List.singleton_append])

def nativeThreeDMRouteCountCompiler : ScalarCompiler (fun s => (nativeThreeDMUnitDrawing decider s).edgeRoutes.length) := by
  apply TM2ComputableInPolyTime.of_eq (countRows (nativeThreeDMIncidenceKeyCompiler decider))
  intro s
  simp only [nativeThreeDMUnitDrawing_routes,List.length_map]

private def unitPeriodCompiler {Symbol : Type} [Fintype Symbol]
    (drawing : List Symbol → PeriodicGridDrawing)
    (base : ScalarCompiler (fun s => (drawing s).gridSize)) :
    ScalarCompiler (fun s => (drawing s).unitSubdivide.gridSize) := base

private def unitVertexFieldsCompiler {Symbol : Type} [Fintype Symbol]
    (drawing : List Symbol → PeriodicGridDrawing)
    (base : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (drawing s).vertexPositions.flatMap PeriodicGridDrawing.Arithmetic.pointFields)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (drawing s).unitSubdivide.vertexPositions.flatMap PeriodicGridDrawing.Arithmetic.pointFields) := base

def nativeThreeDMDrawingPeriodCompiler : ScalarCompiler (fun s => (nativeThreeDMUnitDrawing decider s).gridSize) := by
  have base : ScalarCompiler (fun s => (nativeThreeDMDrawing decider s).gridSize) := by
    apply TM2ComputableInPolyTime.of_eq (nativeThreeDMPeriodCompiler decider)
    intro s
    exact congrArg List.singleton (nativeThreeDMDrawing_period decider s).symm
  exact unitPeriodCompiler (nativeThreeDMDrawing decider) base

def nativeThreeDMDrawingFieldsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => PeriodicGridDrawing.Arithmetic.fields (nativeThreeDMUnitDrawing decider s)) :=
  PeriodicGridDrawing.NativeCompiler.fieldsCompiler (nativeThreeDMUnitDrawing decider)
    (nativeThreeDMDrawingPeriodCompiler decider) (nativeThreeDMSegmentFieldsCompiler decider)
    (unitVertexFieldsCompiler (nativeThreeDMDrawing decider) (nativeThreeDMVertexFieldsCompiler decider))
    (assembleTrailer (nativeThreeDMUnitDrawing decider)
      (nativeThreeDMRouteCountCompiler decider) (nativeThreeDMRouteFieldsCompiler decider))

def nativeThreeDMPlanarInput (s : List encoding.Γ) : NormalizationCompiler.Input :=
  ⟨nativeThreeDMProblem decider s,nativeThreeDMUnitDrawing decider s⟩

def nativeThreeDMPlanarEncodingCompiler : TM2ComputableInPolyTime id FlatEncoding.Planar.finEncoding.encode
    (nativeThreeDMPlanarInput decider) :=
  FlatEncoding.Planar.encodingCompiler (input := nativeThreeDMPlanarInput decider)
    (nativeThreeDMFieldsCompiler decider) (nativeThreeDMDrawingFieldsCompiler decider)

end LeanTrominoes.PeriodicCNFStripReduction
end
