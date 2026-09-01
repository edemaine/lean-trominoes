/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedClauseDescriptorArity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedOccurrenceBlockCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedScopedAtomWordData

/-! # Direct copied-clause scoped final atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCopiedScopedAtomWordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCopiedScopedAtomWordDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Global atom-identifying words for the copied Figure 9 prefix.  Genuine
source atoms inherit their compact pre-Figure9 word; every auxiliary or fresh
polarity atom receives a parent-clause-indexed finite local code. -/
def directSourceFinalCopiedScopedAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  HorizontalRoutedRouteHeaderCopiedScopedAtomWords.words
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)

/-- The aligned pre-Figure9 word column contains exactly the total literal
arity requested by the copied-clause descriptors. -/
theorem directSourceFinalCopiedScopedAtomWords_sourceLength
    (symbols : List encoding.Γ) :
    (directSourceFinalCompactOccurrenceAtomWords decider symbols).words.length =
      ((directRetainedFigureNineCopiedClauseDescriptors decider symbols).map
        retainedFinalCopiedDescriptorArity).sum := by
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_deduplicatedClauses]
  rw [directSourceFinalCopiedClauseDescriptorAritySum_eq]
  unfold PeriodicCNF.presentationLiteralCount
  rw [finalCoordinatedSource_erase_clauses_eq]
  simp

/-- The scoped atom-word column remains aligned one-for-one with the exact
compiled copied occurrence-data prefix. -/
theorem directSourceFinalCopiedScopedAtomWords_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedScopedAtomWords decider symbols).words.length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedScopedAtomWords
    directSourceFinalCopiedOccurrenceData
  exact HorizontalRoutedRouteHeaderCopiedScopedAtomWords.words_length _ _

end PeriodicCNFStripReduction
end LeanTrominoes

end
