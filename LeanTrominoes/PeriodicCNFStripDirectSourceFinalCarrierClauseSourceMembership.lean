/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierClauseGenericLookup

/-! # Direct-source membership of final carrier clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierClauseSourceMembershipStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierClauseSourceMembershipVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every direct final-carrier implication occupies its declared global index
in the duplicate-free final direct-source clause presentation. -/
theorem directSourceFinalCarrierClauses_indexedMember
    (symbols : List encoding.Γ) :
    ∀ taggedClause ∈
        (directSourceFinalCarrierClauses decider symbols).zipIdx
          (directSourceFinalCarrierStart decider symbols),
      taggedClause ∈
        (deduplicatedClauses
          (directSourceFormula decider symbols)).zipIdx := by
  rw [directSourceFormula_eq_finalNormalized decider symbols]
  simpa only [directSourceFinalNormalizedFormula] using
    directSourceFinalCarrierClauses_normalizedIndexedMember
      decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
