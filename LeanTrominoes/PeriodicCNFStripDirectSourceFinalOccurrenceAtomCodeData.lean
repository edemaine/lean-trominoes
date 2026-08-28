/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomCode
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses
import LeanTrominoes.RetainedAngularFanFinalCoordinatedOccurrenceStableRank
import LeanTrominoes.RetainedAngularOccurrenceGlobalAtomCodeSemantics

/-! # Final direct-source occurrence atom-code column -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceFinalOccurrenceAtomCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceFinalOccurrenceAtomCodeVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Presentation-ordered atom codes of the exact source-scaled formula used
by the final stable terminal-rank computation. -/
def directSourceFinalOccurrenceAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  retainedOccurrenceGlobalAtomCodes
    (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase
    directSourceFinalAtomCode

/-- Source-clearance scaling changes offsets but not the aligned atom-code
column. -/
theorem directSourceFinalOccurrenceAtomCodes_eq_unscaled
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceAtomCodes decider symbols =
      retainedOccurrenceGlobalAtomCodes
        (finalCoordinatedSource
          (directSourceFormula decider symbols)).erase
        directSourceFinalAtomCode := by
  unfold directSourceFinalOccurrenceAtomCodes
    retainedOccurrenceGlobalAtomCodes
    retainedFinalCoordinatedScaledSource
    PeriodicThreeSATThree.allOccurrenceVariables
    PeriodicThreeSATThree.taggedLiterals
  simp [PositionedPeriodicCNF.erase_scale,
    List.map_flatMap, Function.comp_def]

/-- Atom codes contributed by one final retained clause. -/
def directSourceFinalClauseAtomCodes
    (clause : PeriodicClause
      (WrappedPeriodicPlanarSATVariable Variable)) : List Nat :=
  clause.map fun literal => directSourceFinalAtomCode literal.atom

/-- The aligned final code column is the clausewise flattening of the exact
deduplicated retained clause presentation. -/
theorem directSourceFinalOccurrenceAtomCodes_eq_deduplicatedClauses
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceAtomCodes decider symbols =
      (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.deduplicatedClauses
        (directSourceFormula decider symbols)).flatMap fun clause =>
          clause.map fun literal => directSourceFinalAtomCode literal.atom := by
  rw [directSourceFinalOccurrenceAtomCodes_eq_unscaled]
  rw [retainedOccurrenceGlobalAtomCodes_eq_clausewise]
  rw [finalCoordinatedSource_erase_clauses_eq]

end PeriodicCNFStripReduction
end LeanTrominoes

end
