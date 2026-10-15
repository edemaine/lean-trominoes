/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalRadialColumnSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Terminal.RetainedAngularFanFinalTerminalCoordinateFamilyPresentation

/-! # Global actual semantics of the final radial column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
