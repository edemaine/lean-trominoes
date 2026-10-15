/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceCompleteTails
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedRayLinearHull

/-! Small linear hulls for the long repeated portions of direct-source routes. -/
namespace LeanTrominoes.PeriodicEightOccurrenceSplit

/-- Replace the repeated staircase by its first and last primitive blocks. -/
def retainedDirectSourceShiftedTailHull (center : Cell) (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  let escape := retainedTerminalFanOuterSourceEscapePoint center terminal slot
  retainedTerminalFanOuterLaneShiftRouteAt escape terminal.1 slot ++
    (retainedTerminalFanOuterEscapedRemainingRay terminal).linearHull
      (Cell.add escape (retainedTerminalFanOuterLaneOffset terminal.1 slot))

/-- Bounds on the hull hold on every point of the shifted tail. -/
theorem retainedDirectSourceShiftedTailHull_linearBounds
    (center normal : Cell) (terminal : RetainedTerminalData) (slot : RetainedTerminalSlot)
    (lower upper : Int)
    (bounded : ∀ point ∈ retainedDirectSourceShiftedTailHull center terminal slot,
      lower ≤ Cell.linearValue normal point ∧ Cell.linearValue normal point ≤ upper)
    {point : Cell}
    (member : point ∈ retainedTerminalFanOuterEscapedShiftedTail center terminal slot) :
    lower ≤ Cell.linearValue normal point ∧ Cell.linearValue normal point ≤ upper := by
  let escape := retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let lane := retainedTerminalFanOuterLaneShiftRouteAt escape terminal.1 slot
  let ray := retainedTerminalFanOuterEscapedRemainingRay terminal
  let start := Cell.add escape (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  change point ∈ joinAtEndpoint lane (ray.rasterize start) at member
  change ∀ point ∈ lane ++ ray.linearHull start,
    lower ≤ Cell.linearValue normal point ∧ Cell.linearValue normal point ≤ upper at bounded
  rcases mem_joinAtEndpoint member with laneMember | rayMember
  · exact bounded point (List.mem_append_left _ laneMember)
  · exact ray.rasterize_linearBounds_of_hull start normal lower upper
      (fun p hp => bounded p (List.mem_append_right _ hp)) rayMember

/-- A small set with the same linear bounds as the complete route. -/
def retainedDirectSourceCompleteRouteHull (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) : List Cell :=
  let center := retainedDirectSourceFanCenterAt kind index
  let terminal := retainedDirectSourceFanTerminalAt kind index
  (retainedDirectSourceFanEscapeAt kind index slot).route ++
    retainedDirectSourceShiftedTailHull center terminal slot ++
      retainedTerminalFanOuterLocalRouteAt center terminal.1 slot

/-- Checking the finite hull suffices to bound the complete route. -/
theorem retainedDirectSourceCompleteRouteHull_linearBounds
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) (normal : Cell) (lower upper : Int)
    (bounded : ∀ point ∈ retainedDirectSourceCompleteRouteHull kind index slot,
      lower ≤ Cell.linearValue normal point ∧ Cell.linearValue normal point ≤ upper)
    {point : Cell} (member : point ∈ retainedDirectSourceFanCompleteRouteAt kind index slot) :
    lower ≤ Cell.linearValue normal point ∧ Cell.linearValue normal point ≤ upper := by
  let center := retainedDirectSourceFanCenterAt kind index
  let terminal := retainedDirectSourceFanTerminalAt kind index
  let escape := (retainedDirectSourceFanEscapeAt kind index slot).route
  let localRoute := retainedTerminalFanOuterLocalRouteAt center terminal.1 slot
  change point ∈ joinAtEndpoint
    (joinAtEndpoint escape (retainedTerminalFanOuterEscapedShiftedTail center terminal slot)) localRoute at member
  change ∀ point ∈ escape ++ retainedDirectSourceShiftedTailHull center terminal slot ++ localRoute,
    lower ≤ Cell.linearValue normal point ∧ Cell.linearValue normal point ≤ upper at bounded
  rcases mem_joinAtEndpoint member with radialMember | localMember
  · rcases mem_joinAtEndpoint radialMember with escapeMember | shiftedMember
    · exact bounded point (List.mem_append_left _ (List.mem_append_left _ escapeMember))
    · exact retainedDirectSourceShiftedTailHull_linearBounds center normal terminal slot lower upper
        (fun p hp => bounded p (List.mem_append_left _ (List.mem_append_right _ hp))) shiftedMember
  · exact bounded point (List.mem_append_right _ localMember)

end LeanTrominoes.PeriodicEightOccurrenceSplit
