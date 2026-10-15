/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalCertificate
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalEqualityCompiler

/-! # Compiler for scaled final terminal-coordinate equality -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalScaledEqualityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Uniform source scaling preserves the semantic equality stream, so the
unscaled direct compiler also compiles the stable-rank input stream. -/
noncomputable def
    directSourceFinalScaledTerminalEqualityBitsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Bool) encoding.Γ Bool id id
      (fun symbols =>
        retainedOccurrenceGlobalTerminalEqualityBits
          (retainedFinalCoordinatedScaledSource
            (directSourceFormula decider symbols)).erase
          (retainedFinalCoordinatedScaledSourceRoutes
            (directSourceFormula decider symbols))) := by
  rw [funext (fun symbols =>
    retainedFinalCoordinatedGlobalTerminalEqualityBits_eq_unscaled
      (directSourceFormula decider symbols)
      (directSourceFinalOccurrenceTerminalCertificate decider symbols))]
  exact directSourceFinalTerminalEqualityBitsComputableInPolyTime decider

end LeanTrominoes.PeriodicCNFStripReduction

end
