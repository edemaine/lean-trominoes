/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverGlobalDeduplication
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverRepresentativeLookup
import LeanTrominoes.RetainedAngularFanFinalDirectSourceMetadataLookup

/-! # Final selector metadata for retained crossovers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- A crossover clause occupying its declared final quotient index selects
a crossover metadata representative in the final direct-source selector. -/
theorem exists_finalCrossoverMetadata_of_clause_lookup
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseLookup :
      (deduplicatedClauses formula)[clauseIndex]? = some clause)
    (crossoverMember :
      clause ∈ crossoverMetadataNormalizedClausesDedup formula) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some metadata ∧
      ∃ crossing localClauseIndex,
        metadata.source = .crossover crossing localClauseIndex := by
  have rawCrossoverMember :
      clause ∈ crossoverMetadataNormalizedClauses formula := by
    simpa [crossoverMetadataNormalizedClausesDedup] using crossoverMember
  rcases exists_crossoverMetadata_global_lookup_of_normalized_mem
      formula clause rawCrossoverMember with
    ⟨metadata, metadataLookup, crossoverSource⟩
  exact ⟨metadata,
    retainedFinalDirectSourceMetadata_eq_some_of_clause_lookup
      formula clauseIndex clause metadata clauseLookup metadataLookup,
    crossoverSource⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
