import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonUnitRoutes

/-!
# Packaging corrected ribbon corridors as three-strand routing

The certified ribbon core stops at the boundary of the source endpoint
macrocells.  This file connects those two boundary points to the existing
finite variable and clause gadget ports and packages the result in the
`ThreeStrandRouting` interface.  Planarity of the endpoint fans is a
separate geometric layer; here the exact endpoints and rectilinearity are
proved.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing

/-- Orthogonal variable-side stub from the finite gadget port to the first
ribbon macrocell boundary. -/
noncomputable def occurrenceRibbonVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  PositionedPeriodicCNF.orthogonalDetour
    (Cell.add
      (constructedVariableOrigin placement
        standardThreeStrandLayout entry.1.1)
      (routedVariablePortPosition source.erase entry color))
    (ribbonCorridorRouteStart color
      (occurrenceUnitSourceRoute presentation entry))

/-- Orthogonal clause-side stub from the final ribbon macrocell boundary to
the finite clause terminal in its referenced periodic translate. -/
noncomputable def occurrenceRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  PositionedPeriodicCNF.orthogonalDetour
    (ribbonCorridorRouteEnd color
      (occurrenceUnitSourceRoute presentation entry))
    (routedClauseTargetPosition source.erase
      (standardThreeStrandLayout.factor * placement.period)
      (constructedClauseOrigin source standardThreeStrandLayout)
      entry color)

/-- Complete corrected colored route: variable stub, certified ribbon core,
and clause stub. -/
noncomputable def occurrenceRibbonThreeStrandRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  joinAtEndpoint
    (joinAtEndpoint
      (occurrenceRibbonVariableStub presentation entry color)
      (occurrenceRibbonCorridorCore presentation entry color))
    (occurrenceRibbonClauseStub presentation entry color)

/-- The corrected route has exactly the finite gadget endpoints required by
the global typed 3DM assembly. -/
theorem occurrenceRibbonThreeStrandRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (occurrenceRibbonThreeStrandRoute
        presentation entry color).head? =
        some (Cell.add
          (constructedVariableOrigin placement
            standardThreeStrandLayout entry.1.1)
          (routedVariablePortPosition source.erase entry color)) ∧
      (occurrenceRibbonThreeStrandRoute
        presentation entry color).getLast? =
        some (routedClauseTargetPosition source.erase
          (standardThreeStrandLayout.factor * placement.period)
          (constructedClauseOrigin source standardThreeStrandLayout)
          entry color) := by
  have coreEndpoints :=
    occurrenceRibbonCorridorCore_endpoints
      presentation entry color
  constructor
  · apply joinAtEndpoint_head?
    apply joinAtEndpoint_head?
    exact PositionedPeriodicCNF.orthogonalDetour_head? _ _
  · apply joinAtEndpoint_getLast?
    · apply joinAtEndpoint_getLast?
      · exact PositionedPeriodicCNF.orthogonalDetour_getLast? _ _
      · exact coreEndpoints.1
      · exact coreEndpoints.2
    · exact PositionedPeriodicCNF.orthogonalDetour_head? _ _
    · exact PositionedPeriodicCNF.orthogonalDetour_getLast? _ _

/-- Every corrected route inherited from a continuously planar source is
rectilinear. -/
theorem occurrenceRibbonThreeStrandRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    OrthogonalPolyline
      (occurrenceRibbonThreeStrandRoute
        presentation.toPlanarIncidencePresentation
        entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  have coreEndpoints :=
    occurrenceRibbonCorridorCore_endpoints
      planar entry color
  have variableStubOrthogonal :
      OrthogonalPolyline
        (occurrenceRibbonVariableStub
          planar entry color) := by
    simp only [occurrenceRibbonVariableStub]
    exact PositionedPeriodicCNF.orthogonalDetour_orthogonal _ _
  have clauseStubOrthogonal :
      OrthogonalPolyline
        (occurrenceRibbonClauseStub
          planar entry color) := by
    simp only [occurrenceRibbonClauseStub]
    exact PositionedPeriodicCNF.orthogonalDetour_orthogonal _ _
  have firstOrthogonal :=
    variableStubOrthogonal.joinAtEndpoint
      (occurrenceRibbonCorridorCore_orthogonal
        presentation entry color)
      (PositionedPeriodicCNF.orthogonalDetour_getLast? _ _)
      coreEndpoints.1
  apply firstOrthogonal.joinAtEndpoint clauseStubOrthogonal
  · apply joinAtEndpoint_getLast?
    · exact PositionedPeriodicCNF.orthogonalDetour_getLast? _ _
    · exact coreEndpoints.1
    · exact coreEndpoints.2
  · exact PositionedPeriodicCNF.orthogonalDetour_head? _ _

/-- A continuously planar exact-one incidence presentation supplies the
corrected endpoint-certified three-strand routing interface. -/
noncomputable def ribbonThreeStrandRouting
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement) :
    ThreeStrandRouting source.erase where
  period :=
    standardThreeStrandLayout.factor * placement.period
  periodPositive :=
    Nat.mul_pos standardThreeStrandLayout.factorPositive
      presentation.periodPositive
  variableOrigin :=
    constructedVariableOrigin placement standardThreeStrandLayout
  clauseOrigin :=
    constructedClauseOrigin source standardThreeStrandLayout
  route :=
    occurrenceRibbonThreeStrandRoute
      presentation.toPlanarIncidencePresentation
  routeEndpoints :=
    occurrenceRibbonThreeStrandRoute_endpoints
      presentation.toPlanarIncidencePresentation
  routeOrthogonal :=
    occurrenceRibbonThreeStrandRoute_orthogonal presentation

/-- Anchor normalization supplies the corrected routing used by the planar
hardness assembly. -/
noncomputable def normalizedRibbonThreeStrandRouting
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    ThreeStrandRouting
      (normalizedPositionedSource source placement).erase :=
  ribbonThreeStrandRouting
    (normalizedRibbonReadyIncidencePresentation presentation
      |>.toContinuousPlanarIncidencePresentation)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
