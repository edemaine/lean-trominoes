/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryInput
import LeanTrominoes.PositionedIncidenceRows
import LeanTrominoes.PeriodicCNFStripDirectGridUnitEmitter
import LeanTrominoes.PeriodicCNFStripHorizontalPeriodSize
import LeanTrominoes.UnaryColumnSignedEncoding

/-! # Geometric certificates and native period of the ordinary SAT endpoint -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing PeriodicCNF PeriodicOrthocrossing UnaryColumn PeriodicPlanarSAT
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryGeometryStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryGeometryVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000

abbrev nativeOrdinaryFormula (s : List encoding.Γ) := ThreeOccurrenceGeometry.formula (directSourceFormula decider s)
abbrev nativeOrdinaryPlacement (s : List encoding.Γ) := ThreeOccurrenceGeometry.placement (directSourceFormula decider s)
abbrev nativeOrdinaryRoutes (s : List encoding.Γ) := ThreeOccurrenceGeometry.routes (directSourceFormula decider s)
abbrev nativeOrdinaryRows (s : List encoding.Γ) := PositionedIncidenceRows.rows (nativeOrdinaryFormula decider s)

theorem nativeOrdinarySource_occurrences (s : List encoding.Γ) :
    @PeriodicCNF.OccurrencesAtMost Variable
      (@instBEqOfDecidableEq Variable ordinaryGeometryVariableDecidableEq) (by infer_instance) 3
      (directSourceFormula decider s) :=
  PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _
    (sourceFormula_occurrencesAtMostThree_canonicalBEq (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))

theorem nativeOrdinaryRoute_endpoints (s : List encoding.Γ) (row : PositionedIncidenceRows.Row OrdinaryVariable)
    (member : row ∈ nativeOrdinaryRows decider s) :
    (nativeOrdinaryRoutes decider s row.1.2 row.2.2).head? = some
      (PositionedPeriodicCNF.canonicalClausePosition (nativeOrdinaryPlacement decider s) row.1.1) ∧
    (nativeOrdinaryRoutes decider s row.1.2 row.2.2).getLast? = some
      (PositionedPeriodicCNF.canonicalLiteralPosition (nativeOrdinaryPlacement decider s) row.1.1 row.2.1) := by
  have hm := (PositionedIncidenceRows.mem_rows _ row).1 member
  have valid := retainedFigureNineClearanceIncidenceRoutes_valid (directSourceFormula decider s)
    (sourceFormula_isLocal _) (sourceFormula_widthAtMostThree _) (nativeOrdinarySource_occurrences decider s)
    (sourceFormula_clausesNonempty _) hm.1 hm.2
  exact ⟨valid.1, valid.2.1⟩

theorem nativeOrdinaryRoute_unitSteps (s : List encoding.Γ) (row : PositionedIncidenceRows.Row OrdinaryVariable)
    (member : row ∈ nativeOrdinaryRows decider s) :
    (nativeOrdinaryRoutes decider s row.1.2 row.2.2).IsChain AxisDirection.IsUnitAxisStep := by
  have hm := (PositionedIncidenceRows.mem_rows _ row).1 member
  exact retainedFigureNineClearanceIncidenceRoutes_unitSteps (directSourceFormula decider s)
    (sourceFormula_isLocal _) (sourceFormula_widthAtMostThree _) (nativeOrdinarySource_occurrences decider s)
    (sourceFormula_clausesNonempty _) hm.1 hm.2

theorem nativeOrdinaryClauses_nonempty (s : List encoding.Γ) :
    ∀ clause ∈ (nativeOrdinaryFormula decider s).clauses, clause.literals ≠ [] :=
  retainedFigureNineClearancePositionedFormula_clausesNonempty (directSourceFormula decider s)
    (sourceFormula_clausesNonempty _)

theorem nativeOrdinaryPeriod_eq (s : List encoding.Γ) :
    (nativeOrdinaryPlacement decider s).period =
      46080 * sourceOrthocrossingGridSize (PolySpaceCompiler.formulaOfSymbols decider s) := by
  simp only [nativeOrdinaryPlacement, ThreeOccurrenceGeometry.placement, retainedFigureNineClearancePlacement,
    PeriodicVariablePlacement.scale_period, retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
    PeriodicEightOccurrenceSplit.retainedAngularFanSourceScaledRefinedPlacement,
    PeriodicEightOccurrenceSplit.retainedAngularFanRefinedPlacement, PeriodicEightOccurrenceSplitPositioned.placement,
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
    wrappedDrawingPeriodicPlanarSATPlacement, drawingPeriodicPlanarSATPlacement,
    retainedFigureNineSourceClearanceFactor, PeriodicEightOccurrenceSplit.retainedTerminalFanRoutingRefinement,
    PeriodicEightOccurrenceSplitPositioned.refinementScale,
    PeriodicEightOccurrenceSplit.retainedAngularFanSourceClearanceFactor, planarMacroScale,
    sourceOrthocrossingGridSize, directSourceFormula]
  have graphCanonical (d : DecidableEq Variable) :
      @PeriodicCNF.incidenceGraph Variable d (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider s)) =
        @PeriodicCNF.incidenceGraph Variable (Classical.decEq _) (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider s)) :=
    congrArg (fun d => @PeriodicCNF.incidenceGraph Variable d (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider s)))
      (Subsingleton.elim _ _)
  simp only [graphCanonical]
  norm_num [Int.toNat]
  ring

theorem nativeOrdinaryPeriod_positive (s : List encoding.Γ) : 0 < (nativeOrdinaryPlacement decider s).period := by
  rw [nativeOrdinaryPeriod_eq]
  exact Nat.mul_pos (by decide) (drawingGridSize_pos _)

def nativeOrdinaryPeriodCompiler : ScalarCompiler (fun s => (nativeOrdinaryPlacement decider s).period) := by
  let base : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => [(directGridUnitsOfSymbols decider s).length]) :=
    TM2CompositionMachine.computableInPolyTime (directGridUnitsOfSymbolsComputableInPolyTime decider)
      UnaryFieldUnitLengthBroadcast.singletonComputableInPolyTime
  let result := TM2CompositionMachine.computableInPolyTime base (UnaryFieldConstantScale.computableInPolyTime 46080)
  simpa only [UnaryFieldConstantScale.values, List.map_cons, List.map_nil, directGridUnitsOfSymbols_length,
    nativeOrdinaryPeriod_eq, Nat.mul_comm] using result

end LeanTrominoes.PeriodicCNFStripReduction
end
