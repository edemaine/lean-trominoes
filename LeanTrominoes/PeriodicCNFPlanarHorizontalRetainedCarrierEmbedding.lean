/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarHorizontalCarrierEmbedding
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedCarrierClauses
import LeanTrominoes.PeriodicCNFPlanarRetainedNormalizationComponents

/-!
# One-dimensional embedded retained-carrier clauses

The typed normalized retained-carrier clause list lets the generic atom-map
theorem be specialized without unfolding the retained-link enumeration.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The embedded normalized retained straight-carrier component is one
dimensional for a horizontal local incidence graph. -/
theorem embeddedNormalizedRetainedCompleteCarrierClauses_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (isLocal : (PeriodicCNF.incidenceGraph formula).IsLocal)
    (horizontal :
      (PeriodicCNF.incidenceGraph formula).HasZeroVerticalOffsets) :
    @PeriodicCNF.IsOneDimensional
      (PeriodicPlanarSATVariable Variable)
      ⟨embeddedNormalizedRetainedCompleteCarrierClauses formula⟩ := by
  have rawHorizontal : PeriodicCNF.IsOneDimensional
      ⟨normalizedRetainedCompleteCarrierClauseList formula⟩ := by
    unfold normalizedRetainedCompleteCarrierClauseList
    exact normalizedRetainedCompleteCarrierClauses_isOneDimensional
      (graph := PeriodicCNF.incidenceGraph formula) isLocal horizontal
  change @PeriodicCNF.IsOneDimensional
    (PeriodicPlanarSATVariable Variable)
    ⟨(normalizedRetainedCompleteCarrierClauseList formula).map
      (@embedPeriodicCarrierClause Variable)⟩
  exact embedPeriodicCarrierClauses_isOneDimensional
    (Variable := Variable)
    (normalizedRetainedCompleteCarrierClauseList formula) rawHorizontal

end PeriodicOrthocrossing
end LeanTrominoes
