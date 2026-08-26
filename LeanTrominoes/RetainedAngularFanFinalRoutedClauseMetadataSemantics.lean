/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseRepresentativeLookup
import LeanTrominoes.RetainedAngularFanFinalDirectSourceMetadataLookup

/-! # Final selector metadata for routed source clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- A routed source clause occupying its declared final quotient index
selects an exact routed-clause metadata representative in the final direct
source selector. -/
theorem exists_finalRoutedClauseMetadata_of_clause_lookup
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
    (routedClauseMember :
      clause ∈ routedClauseMetadataNormalizedClauses formula) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some metadata ∧
      normalizedClause formula metadata = clause ∧
      ∃ (taggedClause : PeriodicClause Variable × Nat)
          (translate : Cell),
        taggedClause ∈ formula.clauses.zipIdx ∧
        translate ∈ neighborTranslations ∧
        metadata = routedClauseMetadataAt formula
          (taggedClause.2, translate) := by
  rcases exists_routedClauseMetadata_global_lookup_of_normalized_mem
      formula wellFormed degree isLocal clause routedClauseMember with
    ⟨metadata, metadataLookup, normalizedEq, sourceWitness⟩
  exact ⟨metadata,
    retainedFinalDirectSourceMetadata_eq_some_of_clause_lookup
      formula clauseIndex clause metadata clauseLookup metadataLookup,
    normalizedEq, sourceWitness⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
