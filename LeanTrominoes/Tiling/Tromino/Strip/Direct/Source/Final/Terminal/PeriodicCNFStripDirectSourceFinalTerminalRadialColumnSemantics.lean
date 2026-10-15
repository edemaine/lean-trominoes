/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Crossover.PeriodicCNFStripDirectSourceFinalCrossoverTerminalColumnSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTerminalRadialSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendTerminalRadialSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Routed.PeriodicCNFStripDirectSourceFinalRoutedTerminalColumnSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalColumnData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalCoordinateFamilySemantics

/-! # Actual semantics of the complete final radial column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalRadialColumnVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The complete compiled five-family radial column is exactly the radial
projection of every actual final terminal coordinate. -/
theorem directSourceFinalTerminalRadialLengths_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalTerminalRadialLengths decider symbols =
      radialLengths
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols)) 0
          (deduplicatedClauses
            (directSourceFormula decider symbols))) := by
  rw [directSourceFinalTerminalCoordinates_eq_families]
  unfold directSourceFinalTerminalRadialLengths
    directSourceFinalCarrierTerminalRadialSuffix
    directSourceFinalBendRoutedTerminalRadialLengths
    radialLengths
  simp only [List.map_append]
  rw [directSourceFinalCrossoverTerminalRadialLengths_eq_actual,
    directSourceFinalCarrierTerminalRadialLengths_eq_actual,
    directSourceFinalBendTerminalRadialLengths_eq_actual,
    directSourceFinalRoutedTerminalRadialLengths_eq_actual]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
