/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCanonical
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaSemantics

/-! # Canonical form of finite direction-ordered formula shapes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeDirectionOrdering

/-- A formula descriptor stream contains all clause tokens before its
distinct-variable suffix, and the fixed clockwise lookup preserves that
canonical layout. -/
theorem shape_ofFormula_isCanonical
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    FormulaShape.IsCanonical (shape (ofFormula source routes)) := by
  unfold FormulaShape.IsCanonical
  rw [clauseProfiles_shape_ofFormula, variableCount_shape_ofFormula]
  rw [shape, ofFormula, List.flatMap_append]
  congr 1
  · rw [List.flatMap_map]
    simp only [tokenBlock, List.map_map]
    change List.flatMap
        (fun taggedClause =>
          [FormulaShape.Token.clause
            (DirectedClauseProfile.ofClause routes
              taggedClause.2 taggedClause.1).orderedProfile])
        source.clauses.zipIdx =
      List.map
        (fun taggedClause =>
          FormulaShape.Token.clause
            (DirectedClauseProfile.ofClause routes
              taggedClause.2 taggedClause.1).orderedProfile)
        source.clauses.zipIdx
    induction source.clauses.zipIdx with
    | nil => rfl
    | cons taggedClause clauses induction =>
        simp [induction]
  · induction source.erase.variableOccurrences.dedup.length with
    | zero => rfl
    | succ count induction =>
        simp [List.replicate_succ, tokenBlock, induction]

end FormulaShapeDirectionOrdering
end PeriodicCNF
end LeanTrominoes
