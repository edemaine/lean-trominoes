/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryRouteSemantics
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryGeometry
import LeanTrominoes.DelimitedDirectionScaling

/-! # Native complete ordinary routes after the final grid refinement -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing PeriodicCNF PeriodicOrthocrossing DelimitedDirectionDisplacement PeriodicPlanarSAT
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryRouteWordStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryRouteWordVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000

def nativeOrdinaryDirectionWords (s : List encoding.Γ) : List (List AxisDirection) :=
  (nativeOrdinaryRows decider s).map (fun row =>
    Gadget.unitSubdivisionDirections (nativeOrdinaryRoutes decider s row.1.2 row.2.2))

theorem nativeOrdinaryRouteDirections_scale (s : List encoding.Γ) (row : PositionedIncidenceRows.Row OrdinaryVariable)
    (member : row ∈ nativeOrdinaryRows decider s) :
    Gadget.unitSubdivisionDirections (nativeOrdinaryRoutes decider s row.1.2 row.2.2) =
      Gadget.repeatDirections 2 (Gadget.unitSubdivisionDirections
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes (directSourceFormula decider s) row.1.2 row.2.2)) := by
  have hm := (PositionedIncidenceRows.mem_rows _ row).1 member
  have eq := retainedFigureNineClearanceIncidenceRoutes_eq_unitSubdividePolyline (directSourceFormula decider s)
    (sourceFormula_isLocal _) (sourceFormula_widthAtMostThree _) (nativeOrdinarySource_occurrences decider s)
    (sourceFormula_clausesNonempty _) hm.1 hm.2
  obtain ⟨clause, hc, clauseEq⟩ := exists_clockwiseClause_of_clearanceClause_mem hm.1
  have hl : row.2 ∈ clause.literals.zipIdx := by simpa only [clauseEq, PositionedPeriodicClause.scale] using hm.2
  have valid := retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid (directSourceFormula decider s)
    (sourceFormula_isLocal _) (sourceFormula_widthAtMostThree _) (nativeOrdinarySource_occurrences decider s)
    (sourceFormula_clausesNonempty _) hc hl
  change Gadget.unitSubdivisionDirections (retainedFigureNineClearanceIncidenceRoutes (directSourceFormula decider s) row.1.2 row.2.2) = _
  rw [eq, Gadget.unitSubdivisionDirections_unitSubdividePolyline _
    (valid.2.2.scalePolyline retainedFigureNineSourceClearanceFactor_pos),
    Gadget.unitSubdivisionDirections_scalePolyline _ retainedFigureNineSourceClearanceFactor_pos]
  rfl

theorem nativeOrdinaryDirectionWords_eq_scaled (s : List encoding.Γ) :
    nativeOrdinaryDirectionWords decider s =
      (nativeOrdinaryParentRouteDirections decider s).map (Gadget.repeatDirections 2) := by
  rw [nativeOrdinaryParentRouteDirections_eq, List.map_map]
  unfold nativeOrdinaryDirectionWords
  calc
    _ = (nativeOrdinaryRows decider s).map (fun row => Gadget.repeatDirections 2
        (Gadget.unitSubdivisionDirections (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
          (directSourceFormula decider s) row.1.2 row.2.2))) :=
      List.map_congr_left (fun row member => nativeOrdinaryRouteDirections_scale decider s row member)
    _ = _ := by
      change (PositionedIncidenceRows.rows
        ((retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula (directSourceFormula decider s)).scale
          retainedFigureNineSourceClearanceFactor)).map _ = _
      simpa only [Function.comp_def] using PositionedIncidenceRows.map_scale_indices
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula (directSourceFormula decider s))
        retainedFigureNineSourceClearanceFactor (fun ci li => Gadget.repeatDirections 2
          (Gadget.unitSubdivisionDirections (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
            (directSourceFormula decider s) ci li)))

def nativeOrdinaryRouteWordsCompiler [Inhabited encoding.Γ] : TM2ComputableInPolyTime id id
    (fun s => words (nativeOrdinaryDirectionWords decider s)) := by
  let physical := TM2CompositionMachine.computableInPolyTime (nativeOrdinaryParentRoutesCompiler decider)
    (FiniteBlockTransducer.computableInPolyTime (scaleToken 2))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [scale_words, nativeOrdinaryDirectionWords_eq_scaled]

end LeanTrominoes.PeriodicCNFStripReduction
end
