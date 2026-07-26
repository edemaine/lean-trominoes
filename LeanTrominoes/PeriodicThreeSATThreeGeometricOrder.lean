import LeanTrominoes.PeriodicCNFPlanarOrderedOneInThreePositioned
import LeanTrominoes.PositionedPeriodicCNFIncidenceDrawing
import Mathlib.Data.List.Sort

/-!
# Occurrence order extracted from incidence-route geometry

Occurrence splitting must connect the copies of a planar variable in the
rotation order of their incident routes.  A positioned incidence
presentation orients every route from its clause to its variable, so the
last route segment determines the direction in which that incidence leaves
the variable when traversed backwards.

This file turns those terminal directions into an executable cyclic order.
Sorting changes only presentation order: the resulting list is proved to be
a permutation of the genuine syntactic occurrence copies and therefore
packages directly as `PeriodicThreeSATThree.OccurrenceOrder`.
-/

namespace LeanTrominoes

namespace PeriodicThreeSATThree

/-- The four directions in cyclic counterclockwise order, followed by a
total fallback for malformed or degenerate routes. -/
inductive TerminalDirection
  | east
  | north
  | west
  | south
  | degenerate
  deriving DecidableEq, Repr

namespace TerminalDirection

/-- Numeric key realizing the declared cyclic order. -/
def rank : TerminalDirection → Nat
  | .east => 0
  | .north => 1
  | .west => 2
  | .south => 3
  | .degenerate => 4

end TerminalDirection

/-- Direction from a route's variable endpoint back along its final
clause-to-variable segment.  Non-axis-aligned, zero-length, and too-short
routes receive the harmless fallback key. -/
def routeTerminalDirection (route : List Cell) : TerminalDirection :=
  match (gridPolylineSegments route).getLast? with
  | none => .degenerate
  | some segment =>
      if segment.start.2 = segment.finish.2 then
        if segment.finish.1 < segment.start.1 then
          .east
        else if segment.start.1 < segment.finish.1 then
          .west
        else
          .degenerate
      else if segment.start.1 = segment.finish.1 then
        if segment.finish.2 < segment.start.2 then
          .north
        else if segment.start.2 < segment.finish.2 then
          .south
        else
          .degenerate
      else
        .degenerate

/-- Terminal direction of the incidence route named by one occurrence
copy's clause and literal indices. -/
def occurrenceTerminalDirection
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (copy : ThreeOccurrenceVariable Variable) :
    TerminalDirection :=
  routeTerminalDirection (routes copy.2.1 copy.2.2)

/-- Boolean comparison used to sort occurrence copies cyclically around
their common variable endpoint. -/
def occurrenceDirectionLE
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (first second : ThreeOccurrenceVariable Variable) : Bool :=
  decide
    ((occurrenceTerminalDirection routes first).rank ≤
      (occurrenceTerminalDirection routes second).rank)

/-- Genuine copies of one variable sorted by their terminal route
directions.  Merge sort is stable, so any fallback ties retain presentation
order. -/
def geometricOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    List (ThreeOccurrenceVariable Variable) :=
  (occurrenceVariables source atom).mergeSort
    (occurrenceDirectionLE routes)

/-- Direction sorting preserves exactly the source variable's genuine
syntactic occurrence copies. -/
theorem geometricOccurrenceVariables_perm
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (geometricOccurrenceVariables source routes atom).Perm
      (occurrenceVariables source atom) := by
  exact List.mergeSort_perm _ _

/-- A lawful occurrence order extracted from the terminal directions of a
route family. -/
def geometricOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    OccurrenceOrder source where
  copies := geometricOccurrenceVariables source routes
  perm := geometricOccurrenceVariables_perm source routes

@[simp]
theorem geometricOccurrenceOrder_copies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (geometricOccurrenceOrder source routes).copies atom =
      geometricOccurrenceVariables source routes atom := by
  rfl

end PeriodicThreeSATThree

namespace PositionedPeriodicCNF

/-- Extract the lawful rotation order carried by a certified planar
incidence presentation.  The permutation property needs only its route
family; planarity will justify the later local cycle routing. -/
def PlanarIncidencePresentation.occurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement) :
    PeriodicThreeSATThree.OccurrenceOrder source.erase :=
  PeriodicThreeSATThree.geometricOccurrenceOrder
    source.erase presentation.routes

end PositionedPeriodicCNF

namespace PeriodicOrthocrossing

/-- Specialize geometric order extraction to the wrapped routed planar SAT
formula that feeds the positioned exact-one pipeline. -/
def drawingOccurrenceOrderOfPresentation
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (presentation :
      PositionedPeriodicCNF.PlanarIncidencePresentation
        (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
        (wrappedDrawingPeriodicPlanarSATPlacement formula)) :
    DrawingOccurrenceOrder formula :=
  presentation.occurrenceOrder

end PeriodicOrthocrossing

end LeanTrominoes
