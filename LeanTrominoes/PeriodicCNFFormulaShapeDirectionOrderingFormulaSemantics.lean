/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingClauseSemantics

/-! # Formula semantics of finite direction-aware shape ordering -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeDirectionOrdering

open ClauseProfileOccurrenceSplit
open UnaryProgramClauseProfile

@[simp] theorem clauseProfiles_shape_ofFormula
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    FormulaShape.clauseProfiles (shape (ofFormula source routes)) =
      source.clauses.zipIdx.map fun taggedClause =>
        (DirectedClauseProfile.ofClause
          routes taggedClause.2 taggedClause.1).orderedProfile := by
  rw [clauseProfiles_shape]
  simp [ofFormula]

@[simp] theorem variableCount_shape_ofFormula
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    FormulaShape.variableCount (shape (ofFormula source routes)) =
      source.erase.variableOccurrences.dedup.length := by
  rw [variableCount_shape]
  simp [ofFormula]

/-- Canonical finite direction descriptors compile to the exact ordered
clause-profile sequence and exact distinct-variable count of route-direction
ordering. -/
theorem shape_ofFormula_correct
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause.literals ≠ []) :
    FormulaShapeOfFormula.CorrectFor
      (shape (ofFormula source routes))
      (PositionedPeriodicCNF.orderClausesByRouteDirection
        source routes).erase := by
  unfold FormulaShapeOfFormula.CorrectFor
  constructor
  · rw [clauseProfiles_shape_ofFormula]
    unfold PositionedPeriodicCNF.orderClausesByRouteDirection
      PositionedPeriodicCNF.erase
    simp only [List.map_map]
    apply List.map_congr_left
    intro taggedClause taggedClauseMember
    apply DirectedClauseProfile.orderedProfile_ofClause_literals
    · exact sourceClausesNonempty taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClauseMember)
    · exact sourceWidth taggedClause.1.literals (by
        change taggedClause.1.literals ∈
          source.clauses.map PositionedPeriodicClause.literals
        exact List.mem_map.mpr
          ⟨taggedClause.1,
            List.fst_mem_of_mem_zipIdx taggedClauseMember, rfl⟩)
  · rw [variableCount_shape_ofFormula]
    exact (PositionedPeriodicCNF.orderClausesByRouteDirection_variableOccurrences_perm
      source routes).dedup.length_eq.symm

end FormulaShapeDirectionOrdering
end PeriodicCNF
end LeanTrominoes
