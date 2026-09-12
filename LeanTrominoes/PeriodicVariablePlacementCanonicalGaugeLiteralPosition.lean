/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-! # Recovering a canonical variable from a bounded literal occurrence -/

namespace LeanTrominoes.PeriodicVariablePlacement

/-- Any physical occurrence in the fundamental square is already the
canonical representative of its variable's periodic orbit. -/
theorem variableGauge_canonicalPositionGauge_position_eq_literalPosition
    {Variable : Type*} (placement : PeriodicVariablePlacement Variable)
    (literal : PeriodicLiteral Variable)
    (inside : 0 ≤ (placement.literalPosition literal).1 ∧
      (placement.literalPosition literal).1 < placement.period ∧
      0 ≤ (placement.literalPosition literal).2 ∧
      (placement.literalPosition literal).2 < placement.period) :
    (placement.variableGauge placement.canonicalPositionGauge).position literal.atom =
      placement.literalPosition literal := by
  rw [variableGauge_canonicalPositionGauge_position]
  have residue :
      ((placement.literalPosition literal).1 % placement.period,
        (placement.literalPosition literal).2 % placement.period) =
      ((placement.position literal.atom).1 % placement.period,
        (placement.position literal.atom).2 % placement.period) := by
    simp [literalPosition, translation, Cell.add, Cell.scale, Int.add_emod]
  rw [← residue, Int.emod_eq_of_lt inside.1 inside.2.1,
    Int.emod_eq_of_lt inside.2.2.1 inside.2.2.2]

end LeanTrominoes.PeriodicVariablePlacement
