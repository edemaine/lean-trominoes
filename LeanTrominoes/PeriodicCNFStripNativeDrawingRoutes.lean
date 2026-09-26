/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeRoutePoints
import LeanTrominoes.DelimitedDirectionRouteFieldsCompiler
import LeanTrominoes.UnaryFieldClosure

/-! # Complete native route-table serialization, including both levels of counts -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn PositionedPeriodicCNF DelimitedDirectionDisplacement
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeDrawingRoutesStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeDrawingRoutesVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

theorem nativeDrawingEdgeRoutes (s : List encoding.Γ) :
    (nativeRoutedDrawing decider s).edgeRoutes =
      (nativeIncidenceRows decider s).map (nativeIncidencePointRoute decider s) := by
  simp only [nativeRoutedDrawing, incidenceDrawing, incidenceEdgeRoutes,
    nativeIncidenceRows, PositionedIncidenceRows.rows, List.map_flatMap, List.map_map,
    Function.comp_def]
  rfl

def nativeDrawingRouteFieldsCompiler [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeRoutedDrawing decider s).edgeRoutes.flatMap PeriodicGridDrawing.Arithmetic.routeFields) := by
  let physical := routeFieldsCompiler (nativeIncidenceRows decider)
    (nativeIncidencePointDirections decider) (nativeIncidencePointStart decider)
    (nativeIncidencePointDirectionsCompiler decider)
    (nativeOffsetClauseColumn decider true true) (nativeOffsetClauseColumn decider true false)
    (nativeOffsetClauseColumn decider false true) (nativeOffsetClauseColumn decider false false)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [nativeDrawingEdgeRoutes, List.flatMap_map]
  exact List.flatMap_congr (fun row member =>
    congrArg PeriodicGridDrawing.Arithmetic.routeFields (nativeIncidencePointRoute_rebuild decider s row member))

def nativeDrawingRouteCountCompiler [Inhabited encoding.Γ] :
    ScalarCompiler (fun s => (nativeRoutedDrawing decider s).edgeRoutes.length) := by
  let lengths := vertexLengthsCompiler
    (fun s => (nativeIncidenceRows decider s).map (nativeIncidencePointDirections decider s))
    (nativeIncidencePointDirectionsCompiler decider)
  let physical := TM2CompositionMachine.computableInPolyTime lengths UnaryFieldAggregate.countCompiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [nativeDrawingEdgeRoutes, List.length_map]

private def assembleTrailer {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (drawing : List Symbol → PeriodicGridDrawing)
    (count : ScalarCompiler (fun s => (drawing s).edgeRoutes.length))
    (fields : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (drawing s).edgeRoutes.flatMap PeriodicGridDrawing.Arithmetic.routeFields)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => PeriodicGridDrawing.Arithmetic.trailer (drawing s)) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _ count fields
  exact TM2ComputableInPolyTime.of_eq physical (fun s => by
    simp only [PeriodicGridDrawing.Arithmetic.trailer, List.singleton_append])

def nativeDrawingTrailerCompilerOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      PeriodicGridDrawing.Arithmetic.trailer (nativeRoutedDrawing decider s)) :=
  assembleTrailer (nativeRoutedDrawing decider)
    (nativeDrawingRouteCountCompiler decider) (nativeDrawingRouteFieldsCompiler decider)

def nativeDrawingTrailerCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      PeriodicGridDrawing.Arithmetic.trailer (nativeRoutedDrawing decider s)) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact nativeDrawingTrailerCompilerOfInhabited decider
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction
end
