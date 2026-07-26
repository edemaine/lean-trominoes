import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorAssembly

/-!
# Unit source routes for 3DM ribbon corridors

This file specializes ordered unit subdivision to every active exact-one
incidence selected by the 3DM reduction.  The resulting source route retains
its exact variable and clause endpoints, has at least two points, remains
orthogonal, and consists entirely of genuine cardinal unit steps.

The separate no-immediate-reversal consequence of source continuous
planarity is intentionally left explicit for the next geometry layer.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing

/-- The source incidence route with every axis-aligned segment subdivided
into ordered unit lattice steps. -/
noncomputable def occurrenceUnitSourceRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) : List Cell :=
  AxisDirection.unitSubdividePolyline
    (occurrenceSourceRoute presentation entry)

/-- The selected rebased source route remains orthogonal. -/
theorem occurrenceSourceRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    OrthogonalPolyline
      (occurrenceSourceRoute presentation entry) := by
  exact
    presentation.variableToClauseRoute_orthogonal
      (occurrenceSpliceData presentation entry).indexedMember

/-- The unitized source route remains orthogonal. -/
theorem occurrenceUnitSourceRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    OrthogonalPolyline
      (occurrenceUnitSourceRoute presentation entry) := by
  exact
    AxisDirection.unitSubdividePolyline_orthogonal
      (occurrenceSourceRoute_orthogonal presentation entry)

/-- Every consecutive pair on the unitized occurrence route is exactly one
genuine cardinal step. -/
theorem occurrenceUnitSourceRoute_unitSteps
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (occurrenceUnitSourceRoute presentation entry).IsChain
      AxisDirection.IsUnitAxisStep := by
  exact
    AxisDirection.unitSubdividePolyline_unitSteps
      (occurrenceSourceRoute_orthogonal presentation entry)

/-- Unit subdivision cannot collapse a genuine incidence route below two
points. -/
theorem occurrenceUnitSourceRoute_length
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    2 ≤ (occurrenceUnitSourceRoute presentation entry).length := by
  have sourceLength :=
    occurrenceSourceRoute_length presentation entry
  have sourceOrthogonal :=
    occurrenceSourceRoute_orthogonal presentation entry
  cases sourceEquation :
      occurrenceSourceRoute presentation entry with
  | nil =>
      simp [sourceEquation] at sourceLength
  | cons first rest =>
      cases rest with
      | nil =>
          simp [sourceEquation] at sourceLength
      | cons second rest =>
          simpa [occurrenceUnitSourceRoute, sourceEquation] using
            AxisDirection.unitSubdividePolyline_length_ge_two
              (first := first) (second := second)
              (rest := rest)
              (by simpa [sourceEquation] using sourceOrthogonal)

/-- Unit subdivision retains the selected incidence's exact source and
target endpoints. -/
theorem occurrenceUnitSourceRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    let data := occurrenceSpliceData presentation entry
    (occurrenceUnitSourceRoute presentation entry).head? =
        some (placement.position data.tagged.1.atom) ∧
      (occurrenceUnitSourceRoute presentation entry).getLast? =
        some (PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1) := by
  let data := occurrenceSpliceData presentation entry
  have nonempty :
      occurrenceSourceRoute presentation entry ≠ [] := by
    intro empty
    have length :=
      occurrenceSourceRoute_length presentation entry
    rw [empty] at length
    simp at length
  constructor
  · rw [occurrenceUnitSourceRoute,
      AxisDirection.unitSubdividePolyline_head? nonempty]
    exact data.routeHead
  · rw [occurrenceUnitSourceRoute,
      AxisDirection.unitSubdividePolyline_getLast?
        nonempty
        (occurrenceSourceRoute_orthogonal
          presentation entry)]
    exact data.routeLast

/-- The endpoint-certified macrocell core assigned to one occurrence and
color. -/
noncomputable def occurrenceRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  ribbonCorridorCore color
    (occurrenceUnitSourceRoute presentation entry)

/-- Exact half-edge-boundary endpoints of the occurrence's colored core. -/
theorem occurrenceRibbonCorridorCore_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (occurrenceRibbonCorridorCore
        presentation entry color).head? =
        some (ribbonCorridorRouteStart color
          (occurrenceUnitSourceRoute presentation entry)) ∧
      (occurrenceRibbonCorridorCore
        presentation entry color).getLast? =
        some (ribbonCorridorRouteEnd color
          (occurrenceUnitSourceRoute presentation entry)) := by
  exact
    ribbonCorridorCore_endpoints_of_length_ge_two color
      (occurrenceUnitSourceRoute_length presentation entry)
      (occurrenceUnitSourceRoute_unitSteps presentation entry)

/-- Once source planarity supplies the no-reversal fact, the occurrence's
macrocell core is rectilinear. -/
theorem occurrenceRibbonCorridorCore_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (occurrenceUnitSourceRoute presentation entry)) :
    OrthogonalPolyline
      (occurrenceRibbonCorridorCore
        presentation entry color) := by
  exact
    ribbonCorridorCore_orthogonal_of_length_ge_two color
      (occurrenceUnitSourceRoute_length presentation entry)
      (occurrenceUnitSourceRoute_unitSteps presentation entry)
      noReversal

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
