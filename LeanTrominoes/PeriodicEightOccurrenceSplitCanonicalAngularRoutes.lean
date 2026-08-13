/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularSplicedRoutes

/-!
# Canonical total angular boundary routes

The angular splice interface can always be instantiated for endpoint and
orthogonality purposes.  This file routes each copied source incidence from
its canonical copied clause position to the corresponding translated fan
boundary using the generic Manhattan detour.

These prefixes intentionally make no noncrossing claim.  They provide a
concrete complete drawing and leave planarity as the sole geometric
obligation for the later planar-orthogonalization layer.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

set_option maxHeartbeats 800000

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Total canonical prefix lookup from copied clauses to angular fan
boundaries. -/
def canonicalAngularBoundaryIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        match clause.literals[literalIndex]? with
        | none => []
        | some literal =>
            PositionedPeriodicCNF.orthogonalDetour
              (PositionedPeriodicCNF.canonicalClausePosition
                (placement sourcePlacement)
                (occurrenceClause
                  (occurrencePortsOfAngularOrder
                    source.erase order)
                  clauseIndex clause))
              (angularFanBoundaryPositionAt
                sourcePlacement literal.atom
                (incidenceRelativeOffset clause literal)
                (angularOccurrenceIndex order literal
                  clauseIndex literalIndex))

/-- Genuine source indices retrieve their advertised canonical boundary
detour. -/
theorem canonicalAngularBoundaryIncidenceRoutes_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    canonicalAngularBoundaryIncidenceRoutes
        source sourcePlacement order
        clauseIndex literalIndex =
      PositionedPeriodicCNF.orthogonalDetour
        (PositionedPeriodicCNF.canonicalClausePosition
          (placement sourcePlacement)
          (occurrenceClause
            (occurrencePortsOfAngularOrder
              source.erase order)
            clauseIndex clause))
        (angularFanBoundaryPositionAt
          sourcePlacement literal.atom
          (incidenceRelativeOffset clause literal)
          (angularOccurrenceIndex order literal
            clauseIndex literalIndex)) := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [canonicalAngularBoundaryIncidenceRoutes,
    clauseLookup, literalLookup]

/-- Canonical Manhattan prefixes instantiate the complete angular boundary
interface for every positioned source and angular occurrence order. -/
def canonicalAngularBoundaryRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase) :
    AngularBoundaryRoutes source sourcePlacement order where
  routes :=
    canonicalAngularBoundaryIncidenceRoutes
      source sourcePlacement order
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    rw [canonicalAngularBoundaryIncidenceRoutes_of_members
      source sourcePlacement order
      clauseMember literalMember]
    simp
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    rw [canonicalAngularBoundaryIncidenceRoutes_of_members
      source sourcePlacement order
      clauseMember literalMember]
    exact PositionedPeriodicCNF.orthogonalDetour_orthogonal _ _

/-- The resulting concrete complete angular-spliced route family. -/
def canonicalAngularSplicedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  angularSplicedIncidenceRoutes
    source sourcePlacement order
    (canonicalAngularBoundaryRoutes
      source sourcePlacement order)

/-- The canonical complete angular-spliced drawing has exact periodic
incidence endpoints. -/
theorem canonicalAngularSplicedIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (sourcePeriodPositive :
      0 < sourcePlacement.period) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement
        (occurrencePortsOfAngularOrder
          source.erase order))
      (placement sourcePlacement)
      (canonicalAngularSplicedIncidenceRoutes
        source sourcePlacement order)).RoutesMatch
      (formula source sourcePlacement
        (occurrencePortsOfAngularOrder
          source.erase order)).erase.incidenceGraph := by
  exact angularSplicedIncidenceDrawing_routesMatch
    source sourcePlacement order
    (canonicalAngularBoundaryRoutes
      source sourcePlacement order)
    sourcePeriodPositive

/-- The canonical complete angular-spliced drawing is orthogonal. -/
theorem canonicalAngularSplicedIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement
        (occurrencePortsOfAngularOrder
          source.erase order))
      (placement sourcePlacement)
      (canonicalAngularSplicedIncidenceRoutes
        source sourcePlacement order)).IsOrthogonal := by
  exact angularSplicedIncidenceDrawing_isOrthogonal
    source sourcePlacement order
    (canonicalAngularBoundaryRoutes
      source sourcePlacement order)

end PeriodicEightOccurrenceSplitPositioned

namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Concrete fully angular-spliced route family for the planarized source
used by the hardness pipeline. -/
def drawingAngularEightOccurrenceSplitPositionedFormula
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplitPositioned.formula
    (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
      input)
    (wrappedDrawingPeriodicPlanarSATPlacement input)
    (PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        input).erase
      (drawingOrderedAngularOccurrenceOrder input))

/-- Refined fixed-eight placement paired with the concrete positioned
formula. -/
def drawingAngularEightOccurrenceSplitPlacement
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplitPositioned.placement
    (wrappedDrawingPeriodicPlanarSATPlacement input)

/-- Forgetting the coordinates recovers the semantic fixed-eight occurrence
split over the positioned source's erasure. -/
@[simp]
theorem drawingAngularEightOccurrenceSplitPositionedFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (drawingAngularEightOccurrenceSplitPositionedFormula
      input).erase =
      PeriodicEightOccurrenceSplit.formula
        (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
          input).erase
        (PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder
          (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
            input).erase
          (drawingOrderedAngularOccurrenceOrder input)) := by
  exact PeriodicEightOccurrenceSplitPositioned.erase_formula
    (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula input)
    (wrappedDrawingPeriodicPlanarSATPlacement input)
    (PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        input).erase
      (drawingOrderedAngularOccurrenceOrder input))

/-- The concrete angular formula uses the established fixed-eight
placement. -/
theorem drawingAngularEightOccurrenceSplitPlacement_eq
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    drawingAngularEightOccurrenceSplitPlacement input =
      drawingEightOccurrenceSplitPlacement input := by
  rfl

def drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        input)
      (wrappedDrawingPeriodicPlanarSATPlacement input)
      (drawingOrderedAngularOccurrenceOrder input)

/-- The concrete hardness-pipeline drawing has exact incidence endpoints. -/
theorem
    drawingEightOccurrenceSplitAngularSplicedIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingAngularEightOccurrenceSplitPositionedFormula input)
      (drawingAngularEightOccurrenceSplitPlacement input)
      (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        input)).RoutesMatch
      (drawingAngularEightOccurrenceSplitPositionedFormula
        input).erase.incidenceGraph := by
  exact
    PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceDrawing_routesMatch
        (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
          input)
        (wrappedDrawingPeriodicPlanarSATPlacement input)
        (drawingOrderedAngularOccurrenceOrder input)
        (drawingPeriodicPlanarSATPlacement_period_pos input)

/-- The concrete hardness-pipeline drawing is orthogonal. -/
theorem
    drawingEightOccurrenceSplitAngularSplicedIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingAngularEightOccurrenceSplitPositionedFormula input)
      (drawingAngularEightOccurrenceSplitPlacement input)
      (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        input)).IsOrthogonal := by
  exact
    PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceDrawing_isOrthogonal
        (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
          input)
        (wrappedDrawingPeriodicPlanarSATPlacement input)
        (drawingOrderedAngularOccurrenceOrder input)

end PeriodicOrthocrossing
end LeanTrominoes
