/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalCertificate
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalStrictLowerCompiler

/-! # Compiler for scaled final terminal-coordinate strict order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalScaledStrictLowerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalScaledStrictLowerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Uniform source scaling preserves the semantic strict-lower stream, so
the unscaled direct compiler also compiles the stable-rank input stream. -/
noncomputable def
    directSourceFinalScaledTerminalStrictLowerBitsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Bool) encoding.Γ Bool id id
      (fun symbols =>
        retainedOccurrenceGlobalTerminalStrictLowerBits
          (retainedFinalCoordinatedScaledSource
            (directSourceFormula decider symbols)).erase
          (retainedFinalCoordinatedScaledSourceRoutes
            (directSourceFormula decider symbols))) := by
  rw [funext (fun symbols =>
    retainedFinalCoordinatedGlobalTerminalStrictLowerBits_eq_unscaled
      (directSourceFormula decider symbols)
      (directSourceFinalOccurrenceTerminalCertificate decider symbols))]
  exact directSourceFinalTerminalStrictLowerBitsComputableInPolyTime decider

end LeanTrominoes.PeriodicCNFStripReduction

end
