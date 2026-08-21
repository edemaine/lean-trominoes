/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataVariableMarkers
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableLengthFormula

/-! # Three-count direct retained metadata variable markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedVariableMarkerCountsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedVariableMarkerCountsDecidableEq :
    DecidableEq Variable := Classical.decEq _

/-- The direct marker suffix has the closed three-count form: two markers per
indexed segment, one per distinct source variable, and thirteen per oriented
crossing. -/
theorem directRetainedPlanarMetadataVariableMarkers_eq_threeCounts
    (symbols : List encoding.Γ) :
    let formula := sourceFormula
      (PolySpaceCompiler.formulaOfSymbols decider symbols)
    directRetainedPlanarMetadataVariableMarkers decider symbols =
      List.replicate
        (2 * (drawing formula.incidenceGraph).indexedSegments.length +
          formula.variableOccurrences.dedup.length +
            13 * (orientedCrossings formula.incidenceGraph).length)
        .variable := by
  let formula := sourceFormula
    (PolySpaceCompiler.formulaOfSymbols decider symbols)
  rw [directRetainedPlanarMetadataVariableMarkers_eq_retainedVariables]
  rw [retainedDrawingPeriodicPlanarSATVariables_length formula
    (PeriodicCNF.incidenceGraph_isLocal
      (sourceFormula_isLocal _))]

end LeanTrominoes.PeriodicCNFStripReduction
