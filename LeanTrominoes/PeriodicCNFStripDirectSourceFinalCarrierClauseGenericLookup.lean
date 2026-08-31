/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierSourceFacts
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.PeriodicThreeSATThreeCarrierClauseLookup

/-! # Direct final-carrier lookup in the normalized formula -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierGenericLookupStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierGenericLookupVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every direct final-carrier implication has the exact lookup declared by
its index in the normalized compiler formula. -/
theorem directSourceFinalCarrierClauses_normalizedIndexedMember
    (symbols : List encoding.Γ) :
    ∀ taggedClause ∈
        (directSourceFinalCarrierClauses decider symbols).zipIdx
          (directSourceFinalCarrierStart decider symbols),
      taggedClause ∈
        (deduplicatedClauses
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols))).zipIdx := by
  intro taggedClause taggedMember
  apply List.mem_zipIdx_iff_getElem?.mpr
  let facts := directThreeCNFSourceFinalCarrierFacts decider symbols
  exact PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses_getElem?_of_mem_zipIdx
    (directThreeCNFSourceFormula decider symbols)
    facts.nonemptyFacts.widthFacts.localFacts.sourceLocal
    facts.nonemptyFacts.widthFacts.sourceWidth
    facts.nonemptyFacts.sourceClausesNonempty
    facts.positiveOffsets
    taggedClause
    (by
      simpa only [directSourceFinalCarrierClauses,
        directSourceFinalCarrierStart,
        directSourceFinalCrossoverClauses] using taggedMember)

end LeanTrominoes.PeriodicCNFStripReduction

end
