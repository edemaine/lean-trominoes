/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Colored.PeriodicCNFStripDirectSourceFinalColoredRoutedRequestBlockSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Compiled.PeriodicCNFStripDirectSourceFinalCompiledOccurrenceData

/-! # Occurrence data carried by explicit direct route pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

/-- The clause-major finite occurrence records and the explicit retained
Figure 9 header/tail pairs are two projections of the same record stream. -/
theorem directSourceFinalCompiledOccurrenceData_eq_routePairs
    (symbols : List encoding.Γ) :
    directSourceFinalCompiledOccurrenceData decider symbols =
      (directFigureNinePolarityRoutePairs decider symbols).map fun pair =>
        HorizontalRoutedRouteHeader.occurrenceData pair.1 := by
  rw [directSourceFinalCompiledOccurrenceData_eq,
    directFigureNinePolarityRouteTailRecords_eq_records,
    HorizontalRoutedRouteHeaderOccurrence.output_records]

end LeanTrominoes.PeriodicCNFStripReduction

end
