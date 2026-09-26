/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryClauseColumns
import LeanTrominoes.DelimitedDirectionVertexCompiler
import LeanTrominoes.DelimitedDirectionRouteFieldsCompiler
import LeanTrominoes.DelimitedDirectionSegmentFieldsCompiler
import LeanTrominoes.UnaryFieldClosure

/-! # Native ordinary route and indexed-segment tables -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn PositionedPeriodicCNF DelimitedDirectionDisplacement
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryDrawingRouteStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryDrawingRouteVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 2048

def nativeOrdinaryDrawing (s : List encoding.Γ) : PeriodicGridDrawing :=
  incidenceDrawing (nativeOrdinaryFormula decider s) (nativeOrdinaryPlacement decider s) (nativeOrdinaryRoutes decider s)

def nativeOrdinaryPointRoute (s : List encoding.Γ) (row : PositionedIncidenceRows.Row OrdinaryVariable) : List Cell :=
  nativeOrdinaryRoutes decider s row.1.2 row.2.2

def nativeOrdinaryPointStart (s : List encoding.Γ) (row : PositionedIncidenceRows.Row OrdinaryVariable) : Cell :=
  canonicalClausePosition (nativeOrdinaryPlacement decider s) row.1.1

def nativeOrdinaryPointDirections (s : List encoding.Γ) (row : PositionedIncidenceRows.Row OrdinaryVariable) : List AxisDirection :=
  Gadget.unitSubdivisionDirections (nativeOrdinaryPointRoute decider s row)

def nativeOrdinaryPointDirectionsCompiler [Inhabited encoding.Γ] : TM2ComputableInPolyTime id id (fun s =>
    words ((nativeOrdinaryRows decider s).map (nativeOrdinaryPointDirections decider s))) := by
  apply TM2ComputableInPolyTime.of_eq (nativeOrdinaryRouteWordsCompiler decider)
  intro s
  simp only [nativeOrdinaryDirectionWords]
  apply congrArg words
  apply List.map_congr_left
  intro row _
  simp only [nativeOrdinaryPointDirections, nativeOrdinaryPointRoute]

theorem nativeOrdinaryPointRoute_rebuild (s : List encoding.Γ) (row : PositionedIncidenceRows.Row OrdinaryVariable)
    (member : row ∈ nativeOrdinaryRows decider s) :
    Gadget.rebuildRoute (nativeOrdinaryPointStart decider s row) (nativeOrdinaryPointDirections decider s row) =
      nativeOrdinaryPointRoute decider s row := by
  have head := (nativeOrdinaryRoute_endpoints decider s row member).1
  have steps := nativeOrdinaryRoute_unitSteps decider s row member
  simp only [nativeOrdinaryPointRoute, nativeOrdinaryPointStart, nativeOrdinaryPointDirections]
  exact (rebuildRoute_eq_vertices
    (canonicalClausePosition (nativeOrdinaryPlacement decider s) row.1.1)
    (Gadget.unitSubdivisionDirections (nativeOrdinaryRoutes decider s row.1.2 row.2.2))).trans
      (unitRoute_eq_vertices (nativeOrdinaryRoutes decider s row.1.2 row.2.2)
        (canonicalClausePosition (nativeOrdinaryPlacement decider s) row.1.1) head steps).symm

theorem nativeOrdinaryDrawingEdgeRoutes (s : List encoding.Γ) :
    (nativeOrdinaryDrawing decider s).edgeRoutes =
      (nativeOrdinaryRows decider s).map (nativeOrdinaryPointRoute decider s) := by
  simp only [nativeOrdinaryDrawing, incidenceDrawing, incidenceEdgeRoutes,
    nativeOrdinaryRows, PositionedIncidenceRows.rows, List.map_flatMap, List.map_map,
    Function.comp_def, nativeOrdinaryPointRoute]

def nativeOrdinaryDrawingRouteFieldsCompiler [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeOrdinaryDrawing decider s).edgeRoutes.flatMap PeriodicGridDrawing.Arithmetic.routeFields) := by
  let physical := routeFieldsCompiler (nativeOrdinaryRows decider)
    (nativeOrdinaryPointDirections decider) (nativeOrdinaryPointStart decider)
    (nativeOrdinaryPointDirectionsCompiler decider)
    (nativeOrdinaryClauseColumn decider true true) (nativeOrdinaryClauseColumn decider true false)
    (nativeOrdinaryClauseColumn decider false true) (nativeOrdinaryClauseColumn decider false false)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [nativeOrdinaryDrawingEdgeRoutes, List.flatMap_map]
  exact List.flatMap_congr (fun row member =>
    congrArg PeriodicGridDrawing.Arithmetic.routeFields (nativeOrdinaryPointRoute_rebuild decider s row member))

def nativeOrdinaryDrawingRouteCountCompiler [Inhabited encoding.Γ] :
    ScalarCompiler (fun s => (nativeOrdinaryDrawing decider s).edgeRoutes.length) := by
  let lengths := vertexLengthsCompiler
    (fun s => (nativeOrdinaryRows decider s).map (nativeOrdinaryPointDirections decider s))
    (nativeOrdinaryPointDirectionsCompiler decider)
  let physical := TM2CompositionMachine.computableInPolyTime lengths UnaryFieldAggregate.countCompiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [nativeOrdinaryDrawingEdgeRoutes, List.length_map]

private def assembleOrdinaryTrailer {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (drawing : List Symbol → PeriodicGridDrawing)
    (count : ScalarCompiler (fun s => (drawing s).edgeRoutes.length))
    (fields : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (drawing s).edgeRoutes.flatMap PeriodicGridDrawing.Arithmetic.routeFields)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => PeriodicGridDrawing.Arithmetic.trailer (drawing s)) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _ count fields
  exact TM2ComputableInPolyTime.of_eq physical (fun s => by
    simp only [PeriodicGridDrawing.Arithmetic.trailer, List.singleton_append])

def nativeOrdinaryDrawingTrailerCompiler [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      PeriodicGridDrawing.Arithmetic.trailer (nativeOrdinaryDrawing decider s)) :=
  assembleOrdinaryTrailer (nativeOrdinaryDrawing decider)
    (nativeOrdinaryDrawingRouteCountCompiler decider) (nativeOrdinaryDrawingRouteFieldsCompiler decider)

def nativeOrdinaryDrawingSegmentFieldsCompiler [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeOrdinaryDrawing decider s).indexedSegments.flatMap PeriodicGridDrawing.Arithmetic.segmentFields) := by
  let physical := segmentFieldsCompiler (nativeOrdinaryRows decider)
    (nativeOrdinaryPointDirections decider) (nativeOrdinaryPointStart decider)
    (nativeOrdinaryPointDirectionsCompiler decider)
    (nativeOrdinaryClauseColumn decider true true) (nativeOrdinaryClauseColumn decider true false)
    (nativeOrdinaryClauseColumn decider false true) (nativeOrdinaryClauseColumn decider false false)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [← segmentTableFields_drawing, nativeOrdinaryDrawingEdgeRoutes]
  apply congrArg segmentTableFields
  exact List.map_congr_left (fun row member => nativeOrdinaryPointRoute_rebuild decider s row member)

end LeanTrominoes.PeriodicCNFStripReduction
end
