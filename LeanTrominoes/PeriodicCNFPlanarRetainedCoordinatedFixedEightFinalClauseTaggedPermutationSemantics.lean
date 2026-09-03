/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseOrderingLookup
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseProfileSemantics
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClausePermutationSemantics

/-! # Tagged final clause permutation of the retained Figure 9 formula -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineFinalClauseOrdering

universe u

/-- Projecting original indices from the reordered tagged literals gives the
same reordered range used by finite Figure 9 coordinates. -/
theorem reorderList_zipIdx_map_snd {Value : Type u}
    (values : List Value) :
    (reorderList values.zipIdx).map Prod.snd =
      reorderList (List.range values.length) := by
  calc
    _ = reorderList (values.zipIdx.map Prod.snd) := by
      exact (reorderList_map Prod.snd values.zipIdx).symm
    _ = _ := by
      rw [List.zipIdx_map_snd, List.range_eq_range']

/-- Total lookup of a reordered literal tag exposes the corresponding entry
of the reordered source-index range. -/
theorem reorderList_zipIdx_getD_snd {Value : Type u}
    (values : List Value) (default : Value) (index : Nat) :
    ((reorderList values.zipIdx).getD index (default, 0)).2 =
      (reorderList (List.range values.length)).getD index 0 := by
  rw [← reorderList_zipIdx_map_snd]
  exact
    (List.getD_map
      (l := reorderList values.zipIdx)
      (d := (default, 0)) (n := index) Prod.snd).symm

end FormulaShapeFigureNineFinalClauseOrdering
end PeriodicCNF

namespace PeriodicOrthocrossing

local instance finalClauseTaggedPermutationVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The semantic second clockwise sort retains the exact original literal
tags: binary clauses use `1,0`, and ternary clauses use `2,0,1`. -/
theorem
    retainedOrderedFixedEight_clauseLiteralOrder_eq_reorderList_zipIdx
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx) :
    PositionedPeriodicCNF.clauseLiteralOrder
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        clauseIndex clause =
      PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList
        clause.literals.zipIdx := by
  have clauseArity :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_clauseArity
      source clauseMember
  rcases clauseArity with binary | ternary
  · rcases List.length_eq_two.mp binary with
      ⟨first, second, literalsEq⟩
    have firstDirection :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_firstDirection_of_binary
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember binary
        (literal := first) (literalIndex := 0) (by simp [literalsEq])
    have secondDirection :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_firstDirection_of_binary
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember binary
        (literal := second) (literalIndex := 1) (by simp [literalsEq])
    simp [PositionedPeriodicCNF.clauseLiteralOrder,
      PositionedPeriodicCNF.clauseLiteralDirectionLE,
      PositionedPeriodicCNF.clauseLiteralDirectionRank,
      AxisDirection.binaryUnitEliminationClauseExitDirection,
      AxisDirection.clockwiseRank, literalsEq,
      firstDirection, secondDirection,
      PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList]
  · rcases List.length_eq_three.mp ternary with
      ⟨first, second, third, literalsEq⟩
    rw [PositionedPeriodicCNF.clauseLiteralOrder_eq_two_zero_one_of_unitEliminationOrder
      (placement :=
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalsEq]
    simp [literalsEq,
      PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList]

end PeriodicOrthocrossing
end LeanTrominoes
