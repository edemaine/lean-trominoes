/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionData

/-! # Exact finite direction semantics of the Figure 7 ring -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFixedEightDirection

open OccurrenceSplitRing

/-- The closed local descriptor stream is precisely its nine clause
descriptors followed by its nine distinct ring-variable markers. -/
theorem cycleDescriptors_eq :
    cycleDescriptors =
      cycleClauseDescriptors ++
        List.replicate FormulaShapeFixedEight.copiesPerVariable .variable := by
  native_decide

@[simp] theorem cycleClauseDescriptors_length :
    cycleClauseDescriptors.length =
      FormulaShapeFixedEight.copiesPerVariable := by
  native_decide

private theorem localCycleFormula_clause_length
    (clause : PeriodicClause RingVertex)
    (clauseMember : clause ∈ localCycleFormula.erase.clauses) :
    clause.length = 2 := by
  change clause ∈
    localCycleFormula.clauses.map PositionedPeriodicClause.literals at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨positionedClause, positionedClauseMember, rfl⟩
  change positionedClause ∈
    cycleFormula.map localCycleClause at positionedClauseMember
  rcases List.mem_map.mp positionedClauseMember with
    ⟨embeddedClause, embeddedClauseMember, rfl⟩
  change embeddedClause ∈
    presentedCycleVertices.map cycleClause at embeddedClauseMember
  rcases List.mem_map.mp embeddedClauseMember with
    ⟨vertex, _, rfl⟩
  simp [localCycleClause, cycleClause]

/-- The closed Figure 7 descriptor block recovers the exact clockwise order
of the local implication ring. -/
theorem cycleShape_correct :
    FormulaShapeOfFormula.CorrectFor
      (FormulaShapeDirectionOrdering.shape cycleDescriptors)
      (PositionedPeriodicCNF.orderClausesByRouteDirection
        localCycleFormula cycleRoutes).erase := by
  exact FormulaShapeDirectionOrdering.shape_ofFormula_correct
    localCycleFormula cycleRoutes
    (by
      intro clause clauseMember
      unfold PeriodicClause.WidthAtMost
      rw [localCycleFormula_clause_length clause clauseMember]
      omega)
    (by
      intro positionedClause positionedClauseMember
      have length := localCycleFormula_clause_length
        positionedClause.literals (by
          change positionedClause.literals ∈
            localCycleFormula.clauses.map PositionedPeriodicClause.literals
          exact List.mem_map.mpr
            ⟨positionedClause, positionedClauseMember, rfl⟩)
      intro empty
      rw [empty] at length
      simp at length)

end FormulaShapeFixedEightDirection
end PeriodicCNF
end LeanTrominoes
