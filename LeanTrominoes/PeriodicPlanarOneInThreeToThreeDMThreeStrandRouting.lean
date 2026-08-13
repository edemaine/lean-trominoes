/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteDrawing

/-!
# Three-strand corridor interface for the planar 3DM reduction

One exact-one incidence becomes three colored 3DM incidences.  The finite
variable-site drawing exposes their distinct RGB ports, and the clause-core
drawing exposes the corresponding distinct terminal vertices.  This file
states the exact rectilinear corridor certificate needed to connect those
ports through the source embedding.

Keeping this interface separate is important: duplicating one planar curve
into three nonintersecting parallel strands is the topological thickening
step of the reduction.  The later list-level 3DM drawing assembly can use
the endpoint and orthogonality fields here without assuming that three
strands are literally the same source route.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- One actually used variable/occurrence-slot pair. -/
abbrev ActiveOccurrenceEntry
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  {entry : Variable × OccurrenceSlot //
    entry ∈ occurrenceEntries source}

/-- The variable component of an active entry occurs in the source. -/
theorem ActiveOccurrenceEntry.atom_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (entry : ActiveOccurrenceEntry source) :
    entry.1.1 ∈ occurringVariables source :=
  ((mem_occurrenceEntries_iff
    source entry.1.1 entry.1.2).mp entry.2).1

/-- The slot component of an active entry is used by its variable. -/
theorem ActiveOccurrenceEntry.slot_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (entry : ActiveOccurrenceEntry source) :
    entry.1.2 ∈ usedSlots source entry.1.1 :=
  ((mem_occurrenceEntries_iff
    source entry.1.1 entry.1.2).mp entry.2).2

/-- The routed typed triple, packaged as an active triple of the checked
finite variable-site drawing. -/
def routedActiveVariableSiteTriple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    ActiveVariableSiteTriple
      (sourceVariableSiteCount source entry.1.1)
      (sourceVariableSiteKind source entry.1.1) :=
  activeVariableSiteTriple source entry.1.1 entry.atom_mem
    entry.1.2 entry.slot_mem
    (routedOccurrenceTriple source entry.1.1 entry.1.2 color)
    (routedOccurrenceTriple_mem_occurrenceTriples
      source entry.1.1 entry.1.2 color)

/-- Relative position of one routed RGB port in the complete finite
variable-site drawing. -/
def routedVariablePortPosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) : Cell :=
  let drawing := sourceVariableSiteDrawing source entry.1.1
  drawing.elementPosition
    (drawing.reference
      (routedActiveVariableSiteTriple source entry color) color)

/-- Relative position of the clause terminal reached by one routed colored
incidence.  The three colors select the three attachment slots in the
terminal group fixed by the source literal index. -/
def routedClausePortPosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source) :
    WireColor → Cell
  | .red =>
      redClauseElementLocalPosition
        (redClauseTerminal source entry.1.1 entry.1.2)
  | .green =>
      greenClauseElementLocalPosition
        (greenClauseTerminal source entry.1.1 entry.1.2)
  | .blue =>
      blueClauseElementLocalPosition
        (blueClauseTerminal source entry.1.1 entry.1.2)

/-- Position of a routed clause terminal in the translate named by its
periodic 3DM reference. -/
def routedClauseTargetPosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (period : Nat) (clauseOrigin : Nat → Cell)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) : Cell :=
  Cell.add
    (Cell.add
      (clauseOrigin
        (occurrenceClauseIndex source entry.1.1 entry.1.2))
      (routedClausePortPosition source entry color))
    (Cell.scale period
      (occurrenceReverseOffset source entry.1.1 entry.1.2))

/-- Certified rectilinear three-strand corridors between all variable-site
connector ports and their translated clause terminals.

`variableOrigin` and `clauseOrigin` reserve the local gadget neighborhoods
inside one physical fundamental square.  `period` is the side length of that
square, so semantic reference offsets are scaled by exactly this value. -/
structure ThreeStrandRouting
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) where
  period : Nat
  periodPositive : 0 < period
  variableOrigin : Variable → Cell
  clauseOrigin : Nat → Cell
  route : ActiveOccurrenceEntry source → WireColor → List Cell
  routeEndpoints :
    ∀ entry color,
      (route entry color).head? =
          some (Cell.add
            (variableOrigin entry.1.1)
            (routedVariablePortPosition source entry color)) ∧
        (route entry color).getLast? =
          some (routedClauseTargetPosition
            source period clauseOrigin entry color)
  routeOrthogonal :
    ∀ entry color,
      PeriodicOrthocrossing.OrthogonalPolyline (route entry color)

namespace ThreeStrandRouting

/-- Physical translation attached to a semantic lattice offset. -/
def periodTranslation
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) (offset : Cell) : Cell :=
  Cell.scale routing.period offset

/-- The endpoint field, exposed with the variable and clause endpoints as
separate conjuncts. -/
theorem route_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    (routing.route entry color).head? =
        some (Cell.add
          (routing.variableOrigin entry.1.1)
          (routedVariablePortPosition source entry color)) ∧
      (routing.route entry color).getLast? =
        some (Cell.add
          (Cell.add
            (routing.clauseOrigin
              (occurrenceClauseIndex
                source entry.1.1 entry.1.2))
            (routedClausePortPosition source entry color))
          (routing.periodTranslation
            (occurrenceReverseOffset
              source entry.1.1 entry.1.2))) := by
  simpa [routedClauseTargetPosition, periodTranslation] using
    routing.routeEndpoints entry color

/-- Every certified corridor is an orthogonal polyline. -/
theorem route_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (routing.route entry color) := by
  exact routing.routeOrthogonal entry color

end ThreeStrandRouting

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
