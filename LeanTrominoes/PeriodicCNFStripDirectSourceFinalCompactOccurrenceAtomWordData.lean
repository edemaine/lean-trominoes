/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactAtomWordSeparation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceAtomCodeFamilies

/-! # Exact final direct-source compact occurrence atom-word column -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCompactAtomWordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCompactAtomWordDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Source-clearance scaling changes offsets but not the aligned compact
atom-word column. -/
theorem directSourceFinalCompactOccurrenceAtomWords_eq_unscaled
    (symbols : List encoding.Γ) :
    directSourceFinalCompactOccurrenceAtomWords decider symbols =
      retainedOccurrenceGlobalAtomWords
        (finalCoordinatedSource
          (directSourceFormula decider symbols)).erase
        (directSourceFinalCompactAtomWord
          (directSourceFormula decider symbols)) := by
  unfold directSourceFinalCompactOccurrenceAtomWords
    retainedOccurrenceGlobalAtomWords
    retainedFinalCoordinatedScaledSource
    PeriodicThreeSATThree.allOccurrenceVariables
    PeriodicThreeSATThree.taggedLiterals
  simp [PositionedPeriodicCNF.erase_scale,
    List.map_flatMap, Function.comp_def]

/-- The final compact word column is the literal-wise flattening of the exact
duplicate-free retained clause presentation. -/
theorem directSourceFinalCompactOccurrenceAtomWords_eq_deduplicatedClauses
    (symbols : List encoding.Γ) :
    (directSourceFinalCompactOccurrenceAtomWords decider symbols).words =
      (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.deduplicatedClauses
        (directSourceFormula decider symbols)).flatMap fun clause =>
          clause.map fun literal =>
            directSourceFinalCompactAtomWord
              (directSourceFormula decider symbols) literal.atom := by
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_unscaled]
  rw [retainedOccurrenceGlobalAtomWords_eq_clausewise]
  rw [finalCoordinatedSource_erase_clauses_eq]

/-- Equivalently, the final compact word column has exactly the five-family
quotient order used by the retained descriptor compiler. -/
theorem directSourceFinalCompactOccurrenceAtomWords_eq_fiveFamilies
    (symbols : List encoding.Γ) :
    (directSourceFinalCompactOccurrenceAtomWords decider symbols).words =
      (directSourceFinalFiveFamilyClauses decider symbols).flatMap
        fun clause => clause.map fun literal =>
          directSourceFinalCompactAtomWord
            (directSourceFormula decider symbols) literal.atom := by
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_deduplicatedClauses]
  rw [directSource_deduplicatedClauses_eq_fiveFamilies]

end PeriodicCNFStripReduction
end LeanTrominoes

end
