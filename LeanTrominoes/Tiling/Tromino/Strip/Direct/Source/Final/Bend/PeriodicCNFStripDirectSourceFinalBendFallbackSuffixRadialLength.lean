/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendTerminalRadialSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Fallback.PeriodicCNFStripDirectSourceFinalFallbackSuffixQueryData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Stable.PeriodicCNFStripDirectSourceFinalStableRankSlotCoordinateLength

/-! # Bend fallback radial-count alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalBendFallbackRadialLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalBendRadialLengths_length_eq_coordinates
    (symbols : List encoding.Γ) :
    (directSourceBaseBendTerminalRadialLengths decider symbols).length =
      (directSourceFinalBendFallbackTerminalCoordinates
        decider symbols).length := by
  rw [directSourceFinalBendTerminalRadialLengths_eq_actual]
  unfold directSourceFinalBendFallbackTerminalCoordinates
    TerminalCoordinateComponents.radialLengths
  simp only [List.length_map]
  exact
    retainedFinalTerminalCoordinatesFrom_finalRoutes_length_irrel
      (directSourceFormula decider symbols)
      (directSourceFinalBendStart decider symbols)
      (directSourceFinalBendClauses decider symbols) _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
