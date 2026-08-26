/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFallbackSemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFamilyPresentation

/-! # List semantics of fallback final copied-clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- An indexed subfamily whose clauses occupy their declared positions and
whose incidences all reject the direct atlas evaluates to the corresponding
canonical retained-metadata descriptor subfamily. -/
theorem
    retainedFinalCopiedClauseDescriptors_indexedFrom_eq_representative
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses :
      List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)))
    (clauseLookups :
      ∀ taggedClause ∈ clauses.zipIdx start,
        (deduplicatedClauses formula)[taggedClause.2]? =
          some taggedClause.1)
    (choicesNone :
      ∀ taggedClause ∈ clauses.zipIdx start,
        ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
          retainedFinalDirectSourceRouteChoice?
              formula taggedClause.2 taggedLiteral.2 = none) :
    retainedFinalCopiedClauseDescriptors
        (retainedFinalIndexedClauseQueriesFrom formula start clauses) =
      clauses.map (representativeClauseDescriptor formula) := by
  induction clauses generalizing start with
  | nil => rfl
  | cons clause clauses induction =>
      have headMember :
          (clause, start) ∈ (clause :: clauses).zipIdx start := by
        simp only [List.zipIdx_cons, List.mem_cons, true_or]
      have headLookup := clauseLookups (clause, start) headMember
      have headChoicesNone :
          ∀ taggedLiteral ∈ clause.zipIdx,
            retainedFinalDirectSourceRouteChoice?
                formula start taggedLiteral.2 = none :=
        choicesNone (clause, start) headMember
      have tailLookups :
          ∀ taggedClause ∈ clauses.zipIdx (start + 1),
            (deduplicatedClauses formula)[taggedClause.2]? =
              some taggedClause.1 := by
        intro taggedClause taggedClauseMember
        exact clauseLookups taggedClause (by
          simp only [List.zipIdx_cons, List.mem_cons]
          exact Or.inr taggedClauseMember)
      have tailChoicesNone :
          ∀ taggedClause ∈ clauses.zipIdx (start + 1),
            ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
              retainedFinalDirectSourceRouteChoice?
                  formula taggedClause.2 taggedLiteral.2 = none := by
        intro taggedClause taggedClauseMember
        exact choicesNone taggedClause (by
          simp only [List.zipIdx_cons, List.mem_cons]
          exact Or.inr taggedClauseMember)
      unfold retainedFinalIndexedClauseQueriesFrom
      simp only [List.zipIdx_cons, List.map_cons,
        retainedFinalCopiedClauseDescriptors, List.flatMap_cons,
        List.singleton_append]
      rw [
        retainedFinalCopiedClauseDescriptorOfQuery_eq_representative_of_choices_none
          formula start clause headLookup headChoicesNone]
      exact congrArg (List.cons (representativeClauseDescriptor formula clause))
        (induction (start + 1) tailLookups tailChoicesNone)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
