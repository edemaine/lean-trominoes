/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFans

/-! # Projections of source clause-ribbon fan data -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

namespace ClauseRibbonFanData

/-- Two clause-fan records are equal when their activity flag and all three
direction fields agree. -/
theorem ext_fields
    (first second : ClauseRibbonFanData)
    (hasRight : first.hasRight = second.hasRight)
    (direction : ∀ group, first.direction group = second.direction group) :
    first = second := by
  cases first with
  | mk firstHasRight firstDirection =>
      cases second with
      | mk secondHasRight secondDirection =>
          simp only at hasRight direction
          cases hasRight
          have directionsEqual : firstDirection = secondDirection :=
            funext direction
          cases directionsEqual
          rfl

end ClauseRibbonFanData

@[simp]
theorem sourceClauseRibbonFanData_hasRight
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (clauseIndex : Nat) :
    (sourceClauseRibbonFanData presentation clauseIndex).hasRight =
      (activeClauseOccurrenceEntries source.erase clauseIndex).any fun entry =>
        decide
          (occurrenceClauseTerminalGroup source.erase entry = .right) := by
  rfl

@[simp]
theorem sourceClauseRibbonFanData_direction_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (clauseIndex : Nat) (group : X3CClauseTerminalGroup) :
    (sourceClauseRibbonFanData presentation clauseIndex).direction group =
      match
        (activeClauseOccurrenceEntries source.erase clauseIndex).find?
          fun entry => decide
            (occurrenceClauseTerminalGroup source.erase entry = group) with
      | some entry => occurrenceSourceClauseDirection presentation entry
      | none => .north := by
  rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
