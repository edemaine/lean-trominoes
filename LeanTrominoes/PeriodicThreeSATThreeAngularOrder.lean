/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOrdered
import LeanTrominoes.PositionedPeriodicCNFIncidenceDrawing
import Mathlib.Data.List.Sort

/-!
# Occurrence order from arbitrary terminal rays

The unsplit routed SAT formula can contain variables of degree greater than
four, notably inside the fixed crossover.  Such a vertex cannot yet have a
strict orthogonal incidence drawing.  Before splitting it, this file retains
the full nonzero integer ray from the variable endpoint back toward its
clause and sorts those rays by polar angle.

Only the permutation law is needed to build a semantic occurrence order.
The later geometric proof will certify that the selected local orders match
the explicit split-gadget drawings.
-/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Vector from a route's variable endpoint back along its final segment.
Malformed routes with no segment receive the total fallback `(0, 0)`. -/
def routeTerminalVector (route : List Cell) : Cell :=
  match (gridPolylineSegments route).getLast? with
  | none => (0, 0)
  | some segment => Cell.sub segment.start segment.finish

@[simp]
theorem routeTerminalVector_pair (source target : Cell) :
    routeTerminalVector [source, target] =
      Cell.sub source target := by
  simp [routeTerminalVector, gridPolylineSegments]

/-- The half-plane beginning at the positive horizontal ray and ending just
before the negative horizontal ray. -/
def terminalVectorUpperHalf (vector : Cell) : Bool :=
  decide
    (0 < vector.2 ∨
      (vector.2 = 0 ∧ 0 ≤ vector.1))

/-- Oriented area of two terminal vectors. -/
def terminalVectorCross (first second : Cell) : Int :=
  first.1 * second.2 - first.2 * second.1

/-- Total polar-angle comparison for terminal vectors.  Nonzero rays are
ordered counterclockwise from east; the zero fallback is placed last.
Collinear rays compare equal. -/
def terminalVectorAngleLE (first second : Cell) : Bool :=
  if first = (0, 0) then
    decide (second = (0, 0))
  else if second = (0, 0) then
    true
  else if terminalVectorUpperHalf first then
    if terminalVectorUpperHalf second then
      decide (0 ≤ terminalVectorCross first second)
    else
      true
  else if terminalVectorUpperHalf second then
    false
  else
    decide (0 ≤ terminalVectorCross first second)

/-- Squared radial distance of a terminal vector from its endpoint. -/
def terminalVectorRadiusSq (vector : Cell) : Int :=
  vector.1 * vector.1 + vector.2 * vector.2

/-- Polar-angle comparison with a canonical radial tie-break.

Collinear rays pointing in the same direction are ordered from their common
endpoint outward.  This is the physical nesting order of their splice gates,
so a later occurrence fan does not have to realize an arbitrary permutation
inside a tied angular block. -/
def terminalVectorAngleRadialLE (first second : Cell) : Bool :=
  decide
    (terminalVectorAngleLE first second = true ∧
      (terminalVectorAngleLE second first = true →
        terminalVectorRadiusSq first ≤
          terminalVectorRadiusSq second))

/-- Full terminal ray of the route named by one occurrence copy. -/
def occurrenceTerminalVector
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (copy : ThreeOccurrenceVariable Variable) : Cell :=
  routeTerminalVector (routes copy.2.1 copy.2.2)

/-- Boolean polar-angle comparison on occurrence copies. -/
def occurrenceAngleLE
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (first second : ThreeOccurrenceVariable Variable) : Bool :=
  terminalVectorAngleRadialLE
    (occurrenceTerminalVector routes first)
    (occurrenceTerminalVector routes second)

/-- Genuine copies sorted by full terminal-ray angle, with collinear ties
ordered from the variable endpoint outward. -/
def angularOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    List (ThreeOccurrenceVariable Variable) :=
  (occurrenceVariables source atom).mergeSort
    (occurrenceAngleLE routes)

/-- Polar-angle sorting preserves exactly the genuine syntactic copies. -/
theorem angularOccurrenceVariables_perm
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (angularOccurrenceVariables source routes atom).Perm
      (occurrenceVariables source atom) := by
  exact List.mergeSort_perm _ _

/-- Lawful occurrence order extracted from arbitrary terminal rays. -/
def angularOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    OccurrenceOrder source where
  copies := angularOccurrenceVariables source routes
  perm := angularOccurrenceVariables_perm source routes

@[simp]
theorem angularOccurrenceOrder_copies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (angularOccurrenceOrder source routes).copies atom =
      angularOccurrenceVariables source routes atom := by
  rfl

end PeriodicThreeSATThree
end LeanTrominoes
