/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTerminalRadialSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Fallback.PeriodicCNFStripDirectSourceFinalFallbackSuffixQueryData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Stable.PeriodicCNFStripDirectSourceFinalStableRankSlotCoordinateLength

/-! # Carrier fallback radial-count alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCarrierFallbackRadialLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalCarrierRadialLengths_length_eq_coordinates
    (symbols : List encoding.Γ) :
    (directSourceCarrierTerminalRadialLengths decider symbols).length =
      (directSourceFinalCarrierFallbackTerminalCoordinates
        decider symbols).length := by
  rw [directSourceFinalCarrierTerminalRadialLengths_eq_actual]
  unfold directSourceFinalCarrierFallbackTerminalCoordinates
    TerminalCoordinateComponents.radialLengths
  simp only [List.length_map]
  exact
    retainedFinalTerminalCoordinatesFrom_finalRoutes_length_irrel
      (directSourceFormula decider symbols)
      (directSourceFinalCarrierStart decider symbols)
      (directSourceFinalCarrierClauses decider symbols) _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
