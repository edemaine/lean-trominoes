/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Compiled.PeriodicCNFStripDirectSourceFinalCompiledRouteTailRecordSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Compiled finite occurrence data for final Figure 9 routes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Project one preliminary header record from every compiled Figure 9
route. Variable fan directions are supplied by `directSourceFinalVariableOccurrenceData`. -/
def directSourceFinalCompiledOccurrenceData
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeader.OccurrenceData :=
  HorizontalRoutedRouteHeaderOccurrence.output
    (directSourceFinalCompiledRouteTailRecords decider symbols)

/-- The complete finite occurrence-data stream is polynomial-time. -/
noncomputable def
    directSourceFinalCompiledOccurrenceDataComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCompiledOccurrenceData decider) := by
  unfold directSourceFinalCompiledOccurrenceData
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCompiledRouteTailRecordsComputableInPolyTime decider)
    HorizontalRoutedRouteHeaderOccurrence.computableInPolyTime

/-- The compiled projection is exactly the finite header projection of the
canonical retained Figure 9 route records. -/
theorem directSourceFinalCompiledOccurrenceData_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCompiledOccurrenceData decider symbols =
      HorizontalRoutedRouteHeaderOccurrence.output
        (directFigureNinePolarityRouteTailRecords decider symbols) := by
  unfold directSourceFinalCompiledOccurrenceData
  rw [directSourceFinalCompiledRouteTailRecords_eq]

end LeanTrominoes.PeriodicCNFStripReduction

end
