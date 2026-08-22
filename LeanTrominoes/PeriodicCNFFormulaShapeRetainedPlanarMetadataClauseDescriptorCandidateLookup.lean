/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapZipIdxLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorCandidateData

/-! # Lookup in retained metadata descriptor candidates -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Looking up a candidate at a normalized-clause index returns the descriptor
at that same stable source index. -/
theorem metadataClauseDescriptorCandidates_getElem?_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause : PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex : Nat)
    (clauseLookup :
      (normalizedClauses source)[clauseIndex]? = some clause) :
    (metadataClauseDescriptorCandidates source)[clauseIndex]? =
      some (metadataClauseDescriptorAt source clause clauseIndex) := by
  unfold metadataClauseDescriptorCandidates
  exact IndexedListScan.map_zipIdx_getElem?_eq_some
    (normalizedClauses source)
    (fun taggedClause =>
      metadataClauseDescriptorAt source taggedClause.1 taggedClause.2)
    clause clauseIndex clauseLookup

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
