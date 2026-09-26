/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryValueColumns
import LeanTrominoes.PeriodicCNFOrdinarySourceRouteProjection
import LeanTrominoes.OrdinarySourceRouteRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompiledRouteTailRecordSemantics

/-! # Complete compiled route words of the ordinary parent clauses -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing PeriodicCNF PeriodicCNF.OrdinarySourceProjection
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryParentRouteStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryParentRouteVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000

def nativeOrdinaryParentRouteDirections (s : List encoding.Γ) : List (List AxisDirection) :=
  (directSourceFinalParentRouteBlocks decider s).flatMap (fun block => (slots block.1).map (fun slot =>
    OrdinarySourceRouteRecord.directions (selectedHeader block.1 slot,
      FormulaShapeFigureNinePolarityRouteTail.selectedTailDirections block.2 (selectedHeader block.1 slot))))

def nativeOrdinaryParentRoutesCompiler [Inhabited encoding.Γ] : TM2ComputableInPolyTime id id
    (fun s => DelimitedDirectionDisplacement.words (nativeOrdinaryParentRouteDirections decider s)) := by
  have records : TM2ComputableInPolyTime id id
      (fun s => HorizontalRoutedRouteHeaderTail.records (directFigureNinePolarityRoutePairs decider s)) :=
    TM2ComputableInPolyTime.of_eq (directSourceFinalCompiledRouteTailRecordsComputableInPolyTime decider)
      (fun s => by
        rw [directSourceFinalCompiledRouteTailRecords_eq, directFigureNinePolarityRouteTailRecords,
          FormulaShapeRetainedFigureNineSourceTail.records,
          FormulaShapeFigureNinePolarityRouteTail.sourceRecords_eq_records]
        rfl)
  have valid (s : List encoding.Γ) (i : Nat) (member : i ∈ nativeOrdinaryQueries decider s) :
      i < (directFigureNinePolarityRoutePairs decider s).length := by
    rw [directSourceFinalParentRouteBlocks_pairs, sourcePairs_blocks]
    apply routeQueries_valid
    simpa only [nativeOrdinaryQueries, directSourceFinalParentRouteBlocks_profiles] using member
  let physical := OrdinarySourceRouteRecord.compiler id (nativeOrdinaryQueries decider)
    (directFigureNinePolarityRoutePairs decider) (nativeOrdinaryQueriesCompiler decider) records valid
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [nativeOrdinaryQueries, directSourceFinalParentRouteBlocks_pairs, sourcePairs_blocks,
    ← directSourceFinalParentRouteBlocks_profiles, queryPairs]
  simp only [nativeOrdinaryParentRouteDirections, List.map_flatMap, List.map_map, Function.comp_def]

end LeanTrominoes.PeriodicCNFStripReduction
end
