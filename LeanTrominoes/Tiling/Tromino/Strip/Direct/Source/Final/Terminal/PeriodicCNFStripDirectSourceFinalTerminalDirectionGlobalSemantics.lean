/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalDirectionColumnSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Terminal.RetainedAngularFanFinalTerminalCoordinateFamilyPresentation

/-! # Global actual semantics of the final direction column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalDirectionGlobalVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The complete compiled direction column is the direction projection of
the authoritative final occurrence-coordinate presentation. -/
theorem directSourceFinalTerminalDirectionRanks_eq_globalCoordinates
    (symbols : List encoding.Γ) :
    directSourceFinalTerminalDirectionRanks decider symbols =
      directionRanks
        (coordinates
          (PeriodicOrthocrossing.finalCoordinatedSource
            (directSourceFormula decider symbols)).erase
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))) := by
  exact (directSourceFinalTerminalDirectionRanks_eq_actual
    decider symbols).trans
      (congrArg directionRanks
        (finalCoordinatedTerminalCoordinates_eq_deduplicatedClauses
          (directSourceFormula decider symbols)).symm)

end LeanTrominoes.PeriodicCNFStripReduction

end
