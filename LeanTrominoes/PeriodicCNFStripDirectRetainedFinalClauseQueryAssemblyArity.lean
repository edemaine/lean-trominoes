/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseDescriptorAssemblyCorrectness
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDeduplicatedClauseShape
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryAritySemantics
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotGrouperData

/-! # Arity alignment of the direct final query assembly -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalAssemblyArityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalAssemblyArityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem retainedFinalCopiedClauseDescriptors_eq_map
    (queries : List RetainedFinalCopiedClauseQuery) :
    retainedFinalCopiedClauseDescriptors queries =
      queries.map retainedFinalCopiedClauseDescriptorOfQuery := by
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      simp only [retainedFinalCopiedClauseDescriptors,
        List.flatMap_cons, List.singleton_append, List.map_cons]
      exact congrArg (List.cons
        (retainedFinalCopiedClauseDescriptorOfQuery query)) induction

/-- Every compiled five-family query declares exactly the length of its
corresponding final duplicate-free clause. -/
theorem directRetainedFinalClauseQueryAssembly_arities_eq_clauseLengths
    (symbols : List encoding.Γ) :
    (directRetainedFinalClauseQueryAssembly decider symbols).map
        FinalOccurrenceRoleSlotGrouper.queryArity =
      (deduplicatedClauses
        (directSourceFormula decider symbols)).map List.length := by
  have descriptorEq :=
    directRetainedFinalClauseDescriptorAssembly_eq_finalCopied
      decider symbols
  calc
    (directRetainedFinalClauseQueryAssembly decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity =
        (directRetainedFinalClauseDescriptorAssembly
          decider symbols).map retainedFinalCopiedDescriptorArity := by
      unfold directRetainedFinalClauseDescriptorAssembly
        FinalOccurrenceRoleSlotGrouper.queryArity
      rw [retainedFinalCopiedClauseDescriptors_eq_map]
      simp only [List.map_map, Function.comp_def,
        retainedFinalCopiedClauseQueryArity_eq_descriptor]
    _ = (retainedFinalCopiedClauseDescriptors
          (retainedFinalIndexedClauseQueries
            (directSourceFormula decider symbols))).map
          retainedFinalCopiedDescriptorArity :=
      congrArg (List.map retainedFinalCopiedDescriptorArity) descriptorEq
    _ = (retainedFinalIndexedClauseQueries
          (directSourceFormula decider symbols)).map
          retainedFinalCopiedClauseQueryArity := by
      rw [retainedFinalCopiedClauseDescriptors_eq_map]
      rw [List.map_map]
      apply List.map_congr_left
      intro query _queryMember
      exact (retainedFinalCopiedClauseQueryArity_eq_descriptor query).symm
    _ = (deduplicatedClauses
          (directSourceFormula decider symbols)).map List.length :=
      retainedFinalIndexedClauseQueries_arities_eq_clauseLengths
        (directSourceFormula decider symbols)
        (directSource_deduplicatedClauses_nonempty decider symbols)
        (directSource_deduplicatedClauses_widthAtMostThree decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
