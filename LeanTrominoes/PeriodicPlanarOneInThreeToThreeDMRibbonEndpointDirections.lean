import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonUnitRoutes

/-!
# Endpoint directions of occurrence ribbon corridors

Each active exact-one incidence supplies a nondegenerate unit route from its
variable endpoint to its clause endpoint.  This file exposes the first and
final cardinal directions of that route and rewrites the two advertised
ribbon-core endpoints as standard macrocell boundary points.  Consequently
the remaining fan geometry depends only on finite gadget data, a color, and
one of four genuine directions.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing

/-- Cardinal direction in which an active source route leaves its variable
endpoint. -/
noncomputable def occurrenceSourceVariableDirection
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    AxisDirection :=
  AxisDirection.polylineFirstDirection
    (occurrenceUnitSourceRoute presentation entry)

/-- Cardinal direction in which an active source route enters its clause
endpoint. -/
noncomputable def occurrenceSourceClauseDirection
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    AxisDirection :=
  AxisDirection.polylineLastDirection
    (occurrenceUnitSourceRoute presentation entry)

/-- Every active route leaves its variable in a genuine cardinal
direction. -/
theorem occurrenceSourceVariableDirection_isGenuine
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (occurrenceSourceVariableDirection
      presentation entry).IsGenuine := by
  exact
    AxisDirection.polylineFirstDirection_isGenuine
      (occurrenceUnitSourceRoute_length presentation entry)
      (occurrenceUnitSourceRoute_unitSteps presentation entry)

/-- Every active route enters its clause in a genuine cardinal direction. -/
theorem occurrenceSourceClauseDirection_isGenuine
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (occurrenceSourceClauseDirection
      presentation entry).IsGenuine := by
  exact
    AxisDirection.polylineLastDirection_isGenuine
      (occurrenceUnitSourceRoute_length presentation entry)
      (occurrenceUnitSourceRoute_unitSteps presentation entry)

/-- Removing a first point from a route containing at least three points
does not change its advertised final ribbon boundary. -/
theorem ribbonCorridorRouteEnd_cons_cons_cons
    (color : WireColor)
    (first second third : Cell) (rest : List Cell) :
    ribbonCorridorRouteEnd color
        (first :: second :: third :: rest) =
      ribbonCorridorRouteEnd color
        (second :: third :: rest) := by
  cases rest <;>
    rfl

/-- On an explicitly displayed final edge, the advertised ribbon endpoint
is the exit boundary of the penultimate source macrocell. -/
theorem ribbonCorridorRouteEnd_append_pair
    (color : WireColor) (leading : List Cell)
    (before last : Cell) :
    ribbonCorridorRouteEnd color
        (leading ++ [before, last]) =
      ribbonMacrocellExit before
        (AxisDirection.between before last) color := by
  induction leading with
  | nil =>
      rfl
  | cons first rest induction =>
      cases rest with
      | nil =>
          rfl
      | cons second rest =>
          cases rest with
          | nil =>
              rw [show
                (first :: second :: []) ++ [before, last] =
                  first :: second :: before :: [last] by
                    simp]
              rw [ribbonCorridorRouteEnd_cons_cons_cons]
              simpa using induction
          | cons third rest =>
              rw [show
                (first :: second :: third :: rest) ++
                    [before, last] =
                  first :: second :: third ::
                    (rest ++ [before, last]) by simp]
              rw [ribbonCorridorRouteEnd_cons_cons_cons]
              simpa using induction

/-- A nondegenerate unit route's final ribbon boundary is equivalently the
entry boundary of its final endpoint macrocell. -/
theorem ribbonCorridorRouteEnd_eq_entry_last
    (color : WireColor) {points : List Cell}
    (length : 2 ≤ points.length)
    (unitSteps :
      points.IsChain AxisDirection.IsUnitAxisStep) :
    ∃ leading before last,
      points = leading ++ [before, last] ∧
        ribbonCorridorRouteEnd color points =
          ribbonMacrocellEntry last
            (AxisDirection.polylineLastDirection points) color := by
  rcases
      AxisDirection.exists_eq_append_pair_of_length_ge_two
        length with
    ⟨leading, before, last, equation⟩
  have finalUnit :
      AxisDirection.IsUnitAxisStep before last := by
    rw [equation] at unitSteps
    exact
      (List.isChain_append_cons_cons.mp unitSteps).2.1
  refine ⟨leading, before, last, equation, ?_⟩
  rw [equation,
    ribbonCorridorRouteEnd_append_pair,
    AxisDirection.polylineLastDirection_append_pair
      leading finalUnit]
  exact
    ribbonMacrocellExit_eq_entry_of_unitAxisStep
      finalUnit color

/-- The occurrence core begins at the standard exit boundary of its source
variable macrocell in the route's first direction. -/
theorem occurrenceRibbonCorridorRouteStart_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    ribbonCorridorRouteStart color
        (occurrenceUnitSourceRoute presentation entry) =
      ribbonMacrocellExit
        (placement.position entry.1.1)
        (occurrenceSourceVariableDirection presentation entry)
        color := by
  let data := occurrenceSpliceData presentation entry
  let points := occurrenceUnitSourceRoute presentation entry
  have length :=
    occurrenceUnitSourceRoute_length presentation entry
  have endpoints :=
    occurrenceUnitSourceRoute_endpoints presentation entry
  have atomEq : data.tagged.1.atom = entry.1.1 :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase entry.1.1 entry.1.2 data.tagged
      data.occurrenceLookup).2
  cases pointsEquation : points with
  | nil =>
      simp [points, pointsEquation] at length
  | cons first rest =>
      cases rest with
      | nil =>
          simp [points, pointsEquation] at length
      | cons second rest =>
          have firstEq :
              first = placement.position entry.1.1 := by
            have headEq := endpoints.1
            rw [show
              occurrenceUnitSourceRoute presentation entry =
                first :: second :: rest by
                  simpa [points] using pointsEquation] at headEq
            simpa [data, atomEq] using headEq
          simp [occurrenceSourceVariableDirection,
            ribbonCorridorRouteStart,
            ribbonCorridorCoreStart,
            points, pointsEquation, firstEq]

/-- The occurrence core finishes at the standard entry boundary of its
source clause endpoint macrocell in the route's final direction. -/
theorem occurrenceRibbonCorridorRouteEnd_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    let data := occurrenceSpliceData presentation entry
    ribbonCorridorRouteEnd color
        (occurrenceUnitSourceRoute presentation entry) =
      ribbonMacrocellEntry
        (PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1)
        (occurrenceSourceClauseDirection presentation entry)
        color := by
  let data := occurrenceSpliceData presentation entry
  let points := occurrenceUnitSourceRoute presentation entry
  have length :=
    occurrenceUnitSourceRoute_length presentation entry
  have unitSteps :=
    occurrenceUnitSourceRoute_unitSteps presentation entry
  have endpoints :=
    occurrenceUnitSourceRoute_endpoints presentation entry
  rcases
      ribbonCorridorRouteEnd_eq_entry_last
        color length unitSteps with
    ⟨leading, before, last, pointsEquation, boundaryEq⟩
  have lastEq :
      last =
        PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1 := by
    have lastEndpoint := endpoints.2
    rw [show
      occurrenceUnitSourceRoute presentation entry =
        leading ++ [before, last] by
          simpa [points] using pointsEquation] at lastEndpoint
    simpa [data] using lastEndpoint
  simpa [points, occurrenceSourceClauseDirection,
    lastEq] using boundaryEq

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
