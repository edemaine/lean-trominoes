/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRepresentativeLookup
import LeanTrominoes.RetainedAngularFanFinalDirectSourceMetadataLookup

/-! # Final selector metadata for retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- A carrier clause occupying its declared final quotient index selects a
carrier metadata representative in the final direct-source selector. -/
theorem exists_finalCarrierMetadata_of_clause_lookup
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clauseIndex : Nat)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseLookup :
      (deduplicatedClauses formula)[clauseIndex]? = some clause)
    (carrierMember : clause ∈ carrierMetadataNormalizedClauses formula) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some metadata ∧
      ∃ link localClauseIndex,
        metadata.source = .carrier link localClauseIndex := by
  rcases exists_carrierMetadata_global_lookup_of_normalized_mem
      formula wellFormed degree isLocal clause carrierMember with
    ⟨metadata, metadataLookup, carrierSource⟩
  exact ⟨metadata,
    retainedFinalDirectSourceMetadata_eq_some_of_clause_lookup
      formula clauseIndex clause metadata clauseLookup metadataLookup,
    carrierSource⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
