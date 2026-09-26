/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionVertexCompiler
import LeanTrominoes.PeriodicCNFStripNativeOffsetColumns
import LeanTrominoes.PeriodicCNFStripNativeRouteGeometry

/-! # Native polynomial-time encoding of all actual incidence-route points -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn DelimitedDirectionDisplacement PositionedPeriodicCNF
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativePointStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativePointVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

def nativeIncidencePointRoute (s : List encoding.Γ) (row : PositionedIncidenceRows.Row RoutedVariable) : List Cell :=
  horizontalRoutedRoutesComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) row.1.2 row.2.2

def nativeIncidencePointStart (s : List encoding.Γ) (row : PositionedIncidenceRows.Row RoutedVariable) : Cell :=
  canonicalClausePosition
    (horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)) row.1.1

def nativeIncidencePointDirections (s : List encoding.Γ) (row : PositionedIncidenceRows.Row RoutedVariable) :
    List AxisDirection := Gadget.unitSubdivisionDirections (nativeIncidencePointRoute decider s row)

def nativeIncidencePointDirectionsCompiler : TM2ComputableInPolyTime id id (fun s =>
    words ((nativeIncidenceRows decider s).map (nativeIncidencePointDirections decider s))) := by
  apply TM2ComputableInPolyTime.of_eq (nativeRouteWordsCompiler decider)
  intro s
  rw [nativeRouteWords, ← PositionedIncidenceRows.directionWords]
  rfl

/-- Exact route reconstruction, not just agreement of endpoints. -/
theorem nativeIncidencePointRoute_rebuild (s : List encoding.Γ)
    (row : PositionedIncidenceRows.Row RoutedVariable) (member : row ∈ nativeIncidenceRows decider s) :
    Gadget.rebuildRoute (nativeIncidencePointStart decider s row) (nativeIncidencePointDirections decider s row) =
      nativeIncidencePointRoute decider s row := by
  have members := (PositionedIncidenceRows.mem_rows _ row).mp member
  have head := (nativeRoutedRoute_endpoints _ members.1 members.2).1
  have steps := nativeRoutedRoute_unitSteps _ members.1 members.2
  exact (rebuildRoute_eq_vertices _ _).trans (unitRoute_eq_vertices _ _ head steps).symm

def nativeIncidencePointFieldsCompilerOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeIncidenceRows decider s).flatMap (fun row =>
        (nativeIncidencePointRoute decider s row).flatMap PeriodicGridDrawing.Arithmetic.pointFields)) := by
  let physical := vertexPointFieldsCompiler (nativeIncidenceRows decider)
    (nativeIncidencePointDirections decider) (nativeIncidencePointStart decider)
    (nativeIncidencePointDirectionsCompiler decider)
    (nativeOffsetClauseColumn decider true true) (nativeOffsetClauseColumn decider true false)
    (nativeOffsetClauseColumn decider false true) (nativeOffsetClauseColumn decider false false)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  exact List.flatMap_congr (fun row member =>
    congrArg (List.flatMap PeriodicGridDrawing.Arithmetic.pointFields)
      (nativeIncidencePointRoute_rebuild decider s row member))

/-- The actual supplied drawing, before atom renaming (which leaves its geometry unchanged). -/
def nativeRoutedDrawing (s : List encoding.Γ) : PeriodicGridDrawing :=
  incidenceDrawing (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))
    (horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))
    (horizontalRoutedRoutesComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))

private theorem incidenceRows_routes {V : Type*} [DecidableEq V]
    (source : PositionedPeriodicCNF V) (placement : PeriodicVariablePlacement V) (routes : IncidenceRoutes) :
    (PositionedIncidenceRows.rows source).map (fun row => routes row.1.2 row.2.2) =
      (incidenceDrawing source placement routes).edgeRoutes := by
  simp only [PositionedIncidenceRows.rows, List.map_flatMap, List.map_map,
    Function.comp_def, incidenceDrawing, incidenceEdgeRoutes]

def nativeDrawingRoutePointFieldsCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeRoutedDrawing decider s).edgeRoutes.flatMap (List.flatMap PeriodicGridDrawing.Arithmetic.pointFields)) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    apply TM2ComputableInPolyTime.of_eq (nativeIncidencePointFieldsCompilerOfInhabited decider)
    intro s
    rw [nativeRoutedDrawing, ← incidenceRows_routes, List.flatMap_map]
    rfl
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction
end
