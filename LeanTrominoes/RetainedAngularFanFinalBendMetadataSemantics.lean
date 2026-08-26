/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRepresentativeLookup
import LeanTrominoes.RetainedAngularFanFinalDirectSourceMetadataLookup

/-! # Final selector metadata for retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- A base-bend clause occupying its declared final quotient index selects
a bend metadata representative in the final direct-source selector. -/
theorem exists_finalBendMetadata_of_clause_lookup
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
    (bendMember : clause ∈ baseBendNormalizedClauses formula) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some metadata ∧
      ∃ routeBend localClauseIndex,
        metadata.source = .bend routeBend localClauseIndex := by
  rcases exists_bendMetadata_global_lookup_of_base_mem
      formula wellFormed degree isLocal clause bendMember with
    ⟨metadata, metadataLookup, bendSource⟩
  exact ⟨metadata,
    retainedFinalDirectSourceMetadata_eq_some_of_clause_lookup
      formula clauseIndex clause metadata clauseLookup metadataLookup,
    bendSource⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
