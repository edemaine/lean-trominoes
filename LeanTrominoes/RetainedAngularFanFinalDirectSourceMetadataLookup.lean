/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRoutes

/-! # Metadata lookup at a final retained clause index -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- A duplicate-free normalized-clause lookup and its first raw metadata
representative compose to the metadata record used by the final direct
selector. -/
theorem retainedFinalDirectSourceMetadata_eq_some_of_clause_lookup
    {Variable : Type} [variableDecEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (clauseLookup :
      (deduplicatedClauses formula)[clauseIndex]? = some clause)
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata formula)[
          (normalizedClauses formula).idxOf clause]? = some metadata) :
    retainedFinalDirectSourceMetadata? formula clauseIndex =
      some metadata := by
  have mappedClauseLookup :
      ((finalCoordinatedSource formula).clauses.map
          PositionedPeriodicClause.literals)[clauseIndex]? =
        some clause := by
    rw [finalCoordinatedSource_clauseLiterals_eq]
    exact clauseLookup
  rw [List.getElem?_map] at mappedClauseLookup
  generalize finalClauseLookup :
      (finalCoordinatedSource formula).clauses[clauseIndex]? =
        finalClauseOption at mappedClauseLookup
  cases finalClauseOption with
  | none => simp at mappedClauseLookup
  | some finalClause =>
      simp only [Option.map_some, Option.some.injEq] at mappedClauseLookup
      have wrappedDecidableEqEq :
          (@instDecidableEqWrappedPeriodicVariable
              (PeriodicPlanarSATVariable Variable)
              (@instDecidableEqPeriodicPlanarSATVariable
                Variable variableDecEq)) =
            (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
              Variable variableDecEq) := by
        funext first second
        exact Subsingleton.elim _ _
      have metadataLookupGeneric := metadataLookup
      rw [← wrappedDecidableEqEq] at metadataLookupGeneric
      unfold retainedFinalDirectSourceMetadata?
      apply retainedRepresentativeItem?_eq_some_of_lookups
        formula (retainedDrawingPlanarSATClauseMetadata formula)
          clauseIndex finalClause metadata
      · exact finalClauseLookup
      · rw [representativeClauseIndex_eq formula,
          mappedClauseLookup]
        exact metadataLookupGeneric

end PeriodicEightOccurrenceSplit
end LeanTrominoes
