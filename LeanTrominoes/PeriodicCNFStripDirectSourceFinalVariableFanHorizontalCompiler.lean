/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanHorizontalSemantics

/-! # Polynomial-time emission of the actual horizontal variable fans -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicPlanarOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The actual normalized horizontal variable fan at each incidence, in
clause-major and literal-minor presentation order. -/
def directSourceFinalHorizontalVariableFans (symbols : List encoding.Γ) : List VariableRibbonFanData :=
  (horizontalSemanticNormalizedRibbonSource
    (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols)).erase.variableOccurrences.map
    (fun atom => horizontalOccurrenceVariableRibbonFanDataComputed
      (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols, atom))

/-- The existing direct machine emits the complete actual horizontal fan
stream in polynomial time, with semantic agreement fully discharged. -/
noncomputable def directSourceFinalHorizontalVariableFansComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalHorizontalVariableFans decider) := by
  apply Turing.TM2ComputableInPolyTime.of_eq
    (directSourceFinalVariableFanDataComputableInPolyTime decider)
  intro symbols
  exact directSourceFinalVariableFanData_eq_horizontal decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
