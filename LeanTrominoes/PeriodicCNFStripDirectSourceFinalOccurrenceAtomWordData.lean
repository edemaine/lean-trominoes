/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIndexedAtomWord
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceAtomCodeFamilies
import LeanTrominoes.RetainedAngularOccurrenceGlobalAtomWordSemantics

/-! # Exact final direct-source occurrence atom-word column -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalOccurrenceAtomWordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalOccurrenceAtomWordVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Presentation-ordered structural words of the exact source-scaled final
formula used by stable terminal ranking. -/
def directSourceFinalOccurrenceAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  retainedOccurrenceGlobalAtomWords
    (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase
    (DirectSourceFinalIndexedAtomWords.word
      (directSourceFormula decider symbols))

/-- Source-clearance scaling changes offsets but not the aligned atom-word
column. -/
theorem directSourceFinalOccurrenceAtomWords_eq_unscaled
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceAtomWords decider symbols =
      retainedOccurrenceGlobalAtomWords
        (finalCoordinatedSource
          (directSourceFormula decider symbols)).erase
        (DirectSourceFinalIndexedAtomWords.word
          (directSourceFormula decider symbols)) := by
  unfold directSourceFinalOccurrenceAtomWords
    retainedOccurrenceGlobalAtomWords
    retainedFinalCoordinatedScaledSource
    PeriodicThreeSATThree.allOccurrenceVariables
    PeriodicThreeSATThree.taggedLiterals
  simp [PositionedPeriodicCNF.erase_scale,
    List.map_flatMap, Function.comp_def]

/-- The final word column is the literal-wise flattening of the exact
duplicate-free retained clause presentation. -/
theorem directSourceFinalOccurrenceAtomWords_eq_deduplicatedClauses
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceAtomWords decider symbols).words =
      (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.deduplicatedClauses
        (directSourceFormula decider symbols)).flatMap fun clause =>
          clause.map fun literal =>
            DirectSourceFinalIndexedAtomWords.word
              (directSourceFormula decider symbols) literal.atom := by
  rw [directSourceFinalOccurrenceAtomWords_eq_unscaled]
  rw [retainedOccurrenceGlobalAtomWords_eq_clausewise]
  rw [finalCoordinatedSource_erase_clauses_eq]

/-- Equivalently, the final word column has exactly the five-family quotient
order used by the retained descriptor compiler. -/
theorem directSourceFinalOccurrenceAtomWords_eq_fiveFamilies
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceAtomWords decider symbols).words =
      (directSourceFinalFiveFamilyClauses decider symbols).flatMap
        fun clause => clause.map fun literal =>
          DirectSourceFinalIndexedAtomWords.word
            (directSourceFormula decider symbols) literal.atom := by
  rw [directSourceFinalOccurrenceAtomWords_eq_deduplicatedClauses]
  rw [directSource_deduplicatedClauses_eq_fiveFamilies]

end PeriodicCNFStripReduction
end LeanTrominoes

end
