/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATCrossoverInternalOccurrences

/-! # Complete variable coverage of the fixed crossover -/

namespace LeanTrominoes.PlanarThreeSAT

/-- All thirteen named variables occur in the fixed Figure 8 crossover
formula. -/
theorem crossoverVariable_mem_crossoverFormula
    (atom : CrossoverVariable) :
    atom ∈ embeddedVariableOccurrences crossoverFormula := by
  cases atom with
  | aLeft =>
      unfold embeddedVariableOccurrences
      apply List.mem_flatMap.mpr
      refine
        ⟨crossoverClause 2 6
            [(.aLeft, true), (.aInnerLeft, false)],
          List.Mem.head _, ?_⟩
      simp [crossoverClause]
  | aInnerLeft =>
      exact crossoverInternal_toVariable_mem_crossoverFormula .aInnerLeft
  | upperLeft =>
      exact crossoverInternal_toVariable_mem_crossoverFormula .upperLeft
  | lowerLeft =>
      exact crossoverInternal_toVariable_mem_crossoverFormula .lowerLeft
  | bTop =>
      unfold embeddedVariableOccurrences
      apply List.mem_flatMap.mpr
      refine
        ⟨crossoverClause 5 2
            [(.bTop, false), (.bInnerTop, true)],
          List.mem_of_mem_drop (i := 7) (List.Mem.head _), ?_⟩
      simp [crossoverClause]
  | bInnerTop =>
      exact crossoverInternal_toVariable_mem_crossoverFormula .bInnerTop
  | center =>
      exact crossoverInternal_toVariable_mem_crossoverFormula .center
  | bInnerBottom =>
      exact crossoverInternal_toVariable_mem_crossoverFormula .bInnerBottom
  | bBottom =>
      unfold embeddedVariableOccurrences
      apply List.mem_flatMap.mpr
      refine
        ⟨crossoverClause 6 10
            [(.bInnerBottom, false), (.bBottom, true)],
          List.mem_of_mem_drop (i := 14) (List.Mem.head _), ?_⟩
      simp [crossoverClause]
  | upperRight =>
      exact crossoverInternal_toVariable_mem_crossoverFormula .upperRight
  | lowerRight =>
      exact crossoverInternal_toVariable_mem_crossoverFormula .lowerRight
  | aInnerRight =>
      exact crossoverInternal_toVariable_mem_crossoverFormula .aInnerRight
  | aRight =>
      unfold embeddedVariableOccurrences
      apply List.mem_flatMap.mpr
      refine
        ⟨crossoverClause 10 5
            [(.aInnerRight, true), (.aRight, false)],
          List.mem_of_mem_drop (i := 24) (List.Mem.head _), ?_⟩
      simp [crossoverClause]

end LeanTrominoes.PlanarThreeSAT
