/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableRepresentativeLookup
import LeanTrominoes.RetainedAngularFanFinalDirectSourceMetadataLookup

/-! # Final selector metadata for routed variables -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- A routed-variable implication occupying its declared final quotient
index selects an exact routed-variable metadata representative in the final
direct-source selector. -/
theorem exists_finalRoutedVariableMetadata_of_clause_lookup
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
    (routedVariableMember :
      clause ∈ routedVariableMetadataNormalizedClauses formula) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some metadata ∧
      normalizedClause formula metadata = clause ∧
      ∃ (site : VariableRouteSite Variable) (armIndex : Nat)
          (arm : DuplicatorArm)
          (link : EqualityLink (PlanarSATNode Variable))
          (forward : Bool),
        site ∈ drawingVariableRouteSites formula ∧
        (link, armIndex) ∈ (routedVariableLinksAt formula site).zipIdx ∧
        arm = link.first.duplicatorArm ∧
        metadata = routedVariableClauseMetadataAt
          site armIndex arm link forward := by
  rcases exists_routedVariableMetadata_global_lookup_of_normalized_mem
      formula wellFormed degree isLocal clause routedVariableMember with
    ⟨metadata, metadataLookup, normalizedEq, sourceWitness⟩
  exact ⟨metadata,
    retainedFinalDirectSourceMetadata_eq_some_of_clause_lookup
      formula clauseIndex clause metadata clauseLookup metadataLookup,
    normalizedEq, sourceWitness⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
