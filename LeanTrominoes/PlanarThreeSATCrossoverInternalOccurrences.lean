/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATCrossoverInternalOccurrenceData

/-! # Internal-variable coverage of the fixed crossover -/

namespace LeanTrominoes.PlanarThreeSAT

/-- Each selected witness is one of the 26 crossover clauses. -/
theorem crossoverInternalWitnessClause_mem_crossoverFormula
    (internal : CrossoverInternal) :
    crossoverInternalWitnessClause internal ∈ crossoverFormula := by
  cases internal with
  | aInnerLeft => exact List.Mem.head _
  | upperLeft =>
      exact List.mem_of_mem_drop (i := 2) (List.Mem.head _)
  | lowerLeft =>
      exact List.mem_of_mem_drop (i := 3) (List.Mem.head _)
  | bInnerTop =>
      exact List.mem_of_mem_drop (i := 2) (List.Mem.head _)
  | center =>
      exact List.mem_of_mem_drop (i := 9) (List.Mem.head _)
  | bInnerBottom =>
      exact List.mem_of_mem_drop (i := 3) (List.Mem.head _)
  | upperRight =>
      exact List.mem_of_mem_drop (i := 12) (List.Mem.head _)
  | lowerRight =>
      exact List.mem_of_mem_drop (i := 13) (List.Mem.head _)
  | aInnerRight =>
      exact List.mem_of_mem_drop (i := 19) (List.Mem.head _)

/-- The selected clause actually contains the selected internal name. -/
theorem crossoverInternal_toVariable_mem_witnessClause
    (internal : CrossoverInternal) :
    internal.toVariable ∈
      (crossoverInternalWitnessClause internal).literals.map Prod.fst := by
  cases internal <;>
    simp [CrossoverInternal.toVariable, crossoverInternalWitnessClause,
      crossoverClause]

/-- Every one of the nine internal names occurs in the fixed Figure 8
crossover formula. -/
theorem crossoverInternal_toVariable_mem_crossoverFormula
    (internal : CrossoverInternal) :
    internal.toVariable ∈ embeddedVariableOccurrences crossoverFormula := by
  unfold embeddedVariableOccurrences
  apply List.mem_flatMap.mpr
  exact ⟨crossoverInternalWitnessClause internal,
    crossoverInternalWitnessClause_mem_crossoverFormula internal,
    crossoverInternal_toVariable_mem_witnessClause internal⟩

end LeanTrominoes.PlanarThreeSAT
