/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierSourceFacts
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.PeriodicThreeSATThreeBendClauseLookup

/-! # Direct final-bend membership in the normalized source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendIndexedMembershipStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendIndexedMembershipVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every direct final-bend implication has the exact global index declared
by the canonical base-bend family of the normalized compiler formula. -/
theorem directSourceFinalBendClauses_normalizedIndexedMember
    (symbols : List encoding.Γ) :
    ∀ taggedClause ∈
        (directSourceFinalBendClauses decider symbols).zipIdx
          (directSourceFinalBendStart decider symbols),
      taggedClause ∈
        (deduplicatedClauses
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols))).zipIdx := by
  intro taggedClause taggedMember
  apply List.mem_zipIdx_iff_getElem?.mpr
  let facts := directThreeCNFSourceFinalCarrierFacts decider symbols
  exact PeriodicThreeSATThree.formulaBaseBendNormalizedClauses_getElem?_of_mem_zipIdx
    (directThreeCNFSourceFormula decider symbols)
    facts.nonemptyFacts.widthFacts.localFacts.sourceLocal
    facts.nonemptyFacts.widthFacts.sourceWidth
    facts.nonemptyFacts.sourceClausesNonempty
    facts.positiveOffsets
    taggedClause
    (by
      simpa only [directSourceFinalBendClauses,
        directSourceFinalBendStart, directSourceFinalCarrierStart,
        directSourceFinalCrossoverClauses,
        directSourceFinalCarrierClauses] using taggedMember)

/-- Thus every indexed direct final-bend clause belongs at the same index in
the duplicate-free final direct-source clause presentation. -/
theorem directSourceFinalBendClauses_indexedMember
    (symbols : List encoding.Γ) :
    ∀ taggedClause ∈
        (directSourceFinalBendClauses decider symbols).zipIdx
          (directSourceFinalBendStart decider symbols),
      taggedClause ∈
        (deduplicatedClauses
          (directSourceFormula decider symbols)).zipIdx := by
  rw [directSourceFormula_eq_finalNormalized decider symbols]
  simpa only [directSourceFinalNormalizedFormula] using
    directSourceFinalBendClauses_normalizedIndexedMember
      decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
