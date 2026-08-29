/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalDirectionSemanticCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalRadialSemanticCompiler
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Compiler for final terminal-coordinate equality -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalTerminalEqualityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalTerminalEqualityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The complete direct terminal columns compile the semantic equality
matrix of final occurrence coordinates. -/
noncomputable def
    directSourceFinalTerminalEqualityBitsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Bool) encoding.Γ Bool id id
      (fun symbols =>
        retainedOccurrenceGlobalTerminalEqualityBits
          (PeriodicOrthocrossing.finalCoordinatedSource
            (directSourceFormula decider symbols)).erase
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    exact retainedOccurrenceGlobalTerminalEqualityBitsComputableInPolyTimeOf
      id
      (fun symbols =>
        (PeriodicOrthocrossing.finalCoordinatedSource
          (directSourceFormula decider symbols)).erase)
      (fun symbols =>
        PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          (directSourceFormula decider symbols))
      (directSourceFinalActualTerminalDirectionRanksComputableInPolyTime
        decider)
      (directSourceFinalActualTerminalRadialLengthsComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
