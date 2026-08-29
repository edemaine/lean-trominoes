/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleSemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryIndexedPresentation

/-! # Arity semantics of final copied-clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- Packing a nonempty width-three literal list preserves its length as the
finite query arity. -/
theorem retainedFinalCopiedClauseQueryOfLiterals_arity_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (literals :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (nonempty : literals ≠ [])
    (width : literals.length ≤ 3) :
    retainedFinalCopiedClauseQueryArity
        (retainedFinalCopiedClauseQueryOfLiterals
          formula clauseIndex literals) =
      literals.length := by
  cases literals with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              cases rest with
              | nil => rfl
              | cons fourth rest =>
                  simp at width
                  omega

/-- The indexed exact query stream has one arity entry equal to the length
of each duplicate-free clause. -/
theorem retainedFinalIndexedClauseQueries_arities_eq_clauseLengths
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clausesNonempty : ∀ clause ∈ deduplicatedClauses formula,
      clause ≠ [])
    (clausesWidth : ∀ clause ∈ deduplicatedClauses formula,
      clause.length ≤ 3) :
    (retainedFinalIndexedClauseQueries formula).map
        retainedFinalCopiedClauseQueryArity =
      (deduplicatedClauses formula).map List.length := by
  unfold retainedFinalIndexedClauseQueries
  rw [List.map_map]
  calc
    _ = (deduplicatedClauses formula).zipIdx.map
        (fun taggedClause => taggedClause.1.length) := by
      apply List.map_congr_left
      intro taggedClause taggedMember
      exact retainedFinalCopiedClauseQueryOfLiterals_arity_eq
        formula taggedClause.2 taggedClause.1
        (clausesNonempty taggedClause.1
          (List.fst_mem_of_mem_zipIdx taggedMember))
        (clausesWidth taggedClause.1
          (List.fst_mem_of_mem_zipIdx taggedMember))
    _ = (deduplicatedClauses formula).map List.length := by
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map List.length)
          (List.zipIdx_map_fst 0 (deduplicatedClauses formula))

end PeriodicEightOccurrenceSplit
end LeanTrominoes
