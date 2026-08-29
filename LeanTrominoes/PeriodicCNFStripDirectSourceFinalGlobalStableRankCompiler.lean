/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomEqualityCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalScaledTerminalEqualityCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalScaledTerminalStrictLowerCompiler
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankComponentCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Compiler for final global stable terminal ranks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGlobalStableRankStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalGlobalStableRankVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The final source-scaled occurrence presentation's exact global stable
terminal-rank stream is polynomial-time computable from direct symbols. -/
noncomputable def
    directSourceFinalGlobalStableTerminalRanksComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat)
      encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (fun symbols =>
        retainedOccurrenceGlobalStableTerminalRanks
          (retainedFinalCoordinatedScaledSource
            (directSourceFormula decider symbols)).erase
          (retainedFinalCoordinatedScaledSourceRoutes
            (directSourceFormula decider symbols))) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    exact
      retainedOccurrenceGlobalStableTerminalRanksComputableInPolyTimeOfComponents
        id
        (fun symbols =>
          (retainedFinalCoordinatedScaledSource
            (directSourceFormula decider symbols)).erase)
        (fun symbols =>
          retainedFinalCoordinatedScaledSourceRoutes
            (directSourceFormula decider symbols))
        (directSourceFinalGlobalAtomEqualityBitsComputableInPolyTime decider)
        (directSourceFinalScaledTerminalStrictLowerBitsComputableInPolyTime
          decider)
        (directSourceFinalScaledTerminalEqualityBitsComputableInPolyTime
          decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact
      TM2EmptyAlphabetListInputCompiler.computableInPolyTime
        UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end
