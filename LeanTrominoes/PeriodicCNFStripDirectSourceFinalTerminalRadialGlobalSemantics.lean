/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalRadialColumnSemantics
import LeanTrominoes.RetainedAngularFanFinalTerminalCoordinateFamilyPresentation

/-! # Global actual semantics of the final radial column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRadialGlobalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRadialGlobalVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The complete compiled radial column is the radial projection of the
authoritative final occurrence-coordinate presentation. -/
theorem directSourceFinalTerminalRadialLengths_eq_globalCoordinates
    (symbols : List encoding.Γ) :
    directSourceFinalTerminalRadialLengths decider symbols =
      radialLengths
        (coordinates
          (PeriodicOrthocrossing.finalCoordinatedSource
            (directSourceFormula decider symbols)).erase
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))) := by
  exact (directSourceFinalTerminalRadialLengths_eq_actual
    decider symbols).trans
      (congrArg radialLengths
        (finalCoordinatedTerminalCoordinates_eq_deduplicatedClauses
          (directSourceFormula decider symbols)).symm)

end LeanTrominoes.PeriodicCNFStripReduction

end
