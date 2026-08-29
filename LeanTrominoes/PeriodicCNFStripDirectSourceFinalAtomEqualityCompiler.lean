/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactAtomWordSeparation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordCompiler

/-! # Compiler for final occurrence atom equality -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalAtomEqualityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalAtomEqualityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compact atom words compile the semantic same-atom square for the
source-scaled final occurrence presentation. -/
noncomputable def
    directSourceFinalGlobalAtomEqualityBitsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Bool) encoding.Γ Bool id id
      (fun symbols =>
        retainedOccurrenceGlobalAtomEqualityBits
          (retainedFinalCoordinatedScaledSource
            (directSourceFormula decider symbols)).erase) := by
  rw [funext
    (directSourceFinalGlobalAtomEqualityBits_eq_compactWords decider)]
  exact
    DelimitedBinaryWordEqualitySquare.equalityBitsComputableInPolyTime
      id
      (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime
        decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
