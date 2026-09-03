/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailPairs
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceTailData

/-! # Source-clause provenance of Figure 9 route pairs -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNinePolarityRouteTail

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineSourceTail

private theorem sourcePairs_replicate_variable_nil
    (count : Nat) :
    sourcePairs
        (List.replicate count Token.variable) [] = [] := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simpa [sourcePairs, List.replicate_succ] using induction

private theorem exists_sourceClause_of_mem_sourcePairsFrom
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauses : List (PositionedPeriodicClause Variable))
    (start variableCount : Nat)
    (pair : Header × List AxisDirection)
    (pairMember : pair ∈
      sourcePairs
        (((clauses.zipIdx start).map fun taggedClause =>
          Token.clause
            (DirectedClauseProfile.ofClause
              routes taggedClause.2 taggedClause.1)) ++
          List.replicate variableCount Token.variable)
        ((clauses.zipIdx start).map fun taggedClause =>
          orderedTailDirections
            routes taggedClause.2 taggedClause.1)) :
    ∃ clause clauseIndex,
      (clause, clauseIndex) ∈ clauses.zipIdx start ∧
      pair.1 ∈ sourceClauseHeaders
        (DirectedClauseProfile.ofClause routes clauseIndex clause) ∧
      pair.2 =
        selectedTailDirections
          (orderedTailDirections routes clauseIndex clause) pair.1 := by
  induction clauses generalizing start with
  | nil =>
      simp only [List.zipIdx_nil, List.map_nil, List.nil_append] at pairMember
      rw [sourcePairs_replicate_variable_nil] at pairMember
      exact False.elim (List.not_mem_nil pairMember)
  | cons clause clauses induction =>
      simp only [List.zipIdx_cons, List.map_cons, List.cons_append,
        sourcePairs, List.mem_append] at pairMember
      rcases pairMember with headMember | tailMember
      · rcases List.mem_map.mp headMember with
          ⟨header, headerMember, pairEq⟩
        subst pair
        refine ⟨clause, start, ?_, headerMember, rfl⟩
        simp [List.zipIdx_cons]
      · rcases induction (start + 1) tailMember with
          ⟨sourceClause, sourceClauseIndex, sourceClauseMember,
            headerMember, tailEq⟩
        refine ⟨sourceClause, sourceClauseIndex, ?_,
          headerMember, tailEq⟩
        rw [List.zipIdx_cons]
        exact List.mem_cons_of_mem _ sourceClauseMember

/-- Every explicit Figure 9 header/tail pair generated from a positioned
formula comes from one genuine source clause.  The witness retains both the
exact directed clause profile and the clockwise tail row consumed alongside
that clause token. -/
theorem exists_sourceClause_of_mem_sourcePairs_ofFormula
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (pair : Header × List AxisDirection)
    (pairMember : pair ∈
      sourcePairs
        (FormulaShapeDirectionOrdering.ofFormula source routes)
        (source.clauses.zipIdx.map fun taggedClause =>
          orderedTailDirections
            routes taggedClause.2 taggedClause.1)) :
    ∃ clause clauseIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx ∧
      pair.1 ∈ sourceClauseHeaders
        (DirectedClauseProfile.ofClause routes clauseIndex clause) ∧
      pair.2 =
        selectedTailDirections
          (orderedTailDirections routes clauseIndex clause) pair.1 := by
  apply exists_sourceClause_of_mem_sourcePairsFrom
    routes source.clauses 0 source.erase.variableOccurrences.dedup.length
    pair
  simpa only [FormulaShapeDirectionOrdering.ofFormula]
    using pairMember

end FormulaShapeFigureNinePolarityRouteTail
end PeriodicCNF
end LeanTrominoes
