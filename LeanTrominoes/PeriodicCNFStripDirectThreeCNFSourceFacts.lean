/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceAtomCodeFamilies
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFOccurrencePositiveOffsets

/-! # Shape facts for the direct width-three source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directThreeCNFSourceFactsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem directThreeCNFSource_isLocal
    (symbols : List encoding.Γ) :
    (directThreeCNFSourceFormula decider symbols).IsLocal := by
  unfold directThreeCNFSourceFormula
  exact PeriodicThreeCNF.formula_isLocal
    (formulaOfSymbols_sourceAdmissible decider symbols).2.1

theorem directThreeCNFSource_widthAtMostThree
    (symbols : List encoding.Γ) :
    (directThreeCNFSourceFormula decider symbols).WidthAtMost 3 := by
  unfold directThreeCNFSourceFormula
  exact PeriodicThreeCNF.formula_widthAtMostThree _

theorem directThreeCNFSource_clausesNonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ (directThreeCNFSourceFormula decider symbols).clauses,
      clause ≠ [] := by
  unfold directThreeCNFSourceFormula
  exact PeriodicThreeCNF.formula_clausesNonempty _
    (formulaOfSymbols_clauses_nonempty decider symbols)

theorem directThreeCNFSource_positiveOffsets
    (symbols : List encoding.Γ) :
    ∀ incidence ∈ PeriodicThreeSATThree.occurrenceIncidences
        (directThreeCNFSourceFormula decider symbols),
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0) := by
  unfold directThreeCNFSourceFormula
  exact directThreeCNFSource_occurrenceIncidences_positiveOffsets
    decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
