/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Crossover.PeriodicCNFStripDirectSourceFinalCrossoverTerminalColumnSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTerminalColumnSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendTerminalColumnSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Routed.PeriodicCNFStripDirectSourceFinalRoutedTerminalColumnSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalColumnData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalCoordinateFamilySemantics

/-! # Actual semantics of the complete final direction column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalDirectionColumnVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The complete compiled five-family direction column is exactly the
direction projection of every actual final terminal coordinate. -/
theorem directSourceFinalTerminalDirectionRanks_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalTerminalDirectionRanks decider symbols =
      directionRanks
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols)) 0
          (deduplicatedClauses
            (directSourceFormula decider symbols))) := by
  rw [directSourceFinalTerminalCoordinates_eq_families]
  unfold directSourceFinalTerminalDirectionRanks
    directSourceFinalCarrierTerminalDirectionRankSuffix
    directSourceFinalBendRoutedTerminalDirectionRanks
    directionRanks
  simp only [List.map_append]
  rw [directSourceFinalCrossoverTerminalDirectionRanks_eq_actual,
    directSourceFinalCarrierTerminalDirectionRanks_eq_actual,
    directSourceFinalBendTerminalDirectionRanks_eq_actual,
    directSourceFinalRoutedTerminalDirectionRanks_eq_actual]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
