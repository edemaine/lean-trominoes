/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanEscapedFirstDirections

/-! # Cardinal classification of singleton fallback source edges -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree

/-- An axis-aligned two-point route can classify only as one of the four
cardinal retained compass terminals. -/
theorem retainedTerminalDirectionClassify_pair_axisAligned_cardinal
    (first second : Cell)
    (terminal : RetainedTerminalData)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector [first, second]) =
        some terminal)
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    ∃ port length,
      terminal = (.compass port, length) ∧
        (port = .north ∨ port = .east ∨
          port = .south ∨ port = .west) ∧
        0 < length := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases terminal with ⟨direction, length⟩
  have lengthPositive :=
    (retainedTerminalDirectionClassify_sound classified).1
  have vectorEq :=
    (retainedTerminalDirectionClassify_sound classified).2
  simp only [routeTerminalVector_pair, Cell.sub,
    Prod.mk.injEq, Cell.scale] at vectorEq
  simp only [GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal, GridSegment.IsVertical] at aligned
  cases direction with
  | compass port =>
      cases port with
      | northwest =>
          exfalso
          simp [RetainedTerminalDirection.primitive,
            Port.unitVector] at vectorEq
          rcases aligned with aligned | aligned <;> simp_all
      | north =>
          exact ⟨.north, length, rfl, Or.inl rfl, lengthPositive⟩
      | northeast =>
          exfalso
          simp [RetainedTerminalDirection.primitive,
            Port.unitVector] at vectorEq
          rcases aligned with aligned | aligned <;> omega
      | east =>
          exact ⟨.east, length, rfl,
            Or.inr (Or.inl rfl), lengthPositive⟩
      | southeast =>
          exfalso
          simp [RetainedTerminalDirection.primitive,
            Port.unitVector] at vectorEq
          rcases aligned with aligned | aligned <;> omega
      | south =>
          exact ⟨.south, length, rfl,
            Or.inr (Or.inr (Or.inl rfl)), lengthPositive⟩
      | southwest =>
          exfalso
          simp [RetainedTerminalDirection.primitive,
            Port.unitVector] at vectorEq
          rcases aligned with aligned | aligned <;> omega
      | west =>
          exact ⟨.west, length, rfl,
            Or.inr (Or.inr (Or.inr rfl)), lengthPositive⟩
  | routedClause arm =>
      cases arm <;>
        exfalso <;>
        simp [RetainedTerminalDirection.primitive,
          routedClauseRayPrimitive,
          Cell.sub] at vectorEq <;>
        rcases aligned with aligned | aligned <;> omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
