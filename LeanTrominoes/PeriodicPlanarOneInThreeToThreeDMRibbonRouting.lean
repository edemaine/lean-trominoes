/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFanSystem

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

/-- The original corrected route is definitionally the route selected by the
packaged independent one-bend fan system. -/
theorem occurrenceRibbonThreeStrandRoute_eq_independentFanSystem
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    occurrenceRibbonThreeStrandRoute presentation entry color =
      RibbonEndpointFanSystem.occurrenceThreeStrandRoute
        (independentOneBendEndpointFanSystem presentation)
        entry color := by
  rfl

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
  have variableEndpoints :=
    occurrenceRibbonVariableStub_endpoints
      presentation entry color
  have clauseEndpoints :=
    occurrenceRibbonClauseStub_endpoints
      presentation entry color
  constructor
  · apply joinAtEndpoint_head?
    apply joinAtEndpoint_head?
    exact variableEndpoints.1
  · apply joinAtEndpoint_getLast?
    · apply joinAtEndpoint_getLast?
      · exact variableEndpoints.2
      · exact coreEndpoints.1
      · exact coreEndpoints.2
    · exact clauseEndpoints.1
    · exact clauseEndpoints.2

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
  have variableEndpoints :=
    occurrenceRibbonVariableStub_endpoints
      planar entry color
  have clauseEndpoints :=
    occurrenceRibbonClauseStub_endpoints
      planar entry color
  have variableStubOrthogonal :
      OrthogonalPolyline
        (occurrenceRibbonVariableStub
          planar entry color) := by
    exact occurrenceRibbonVariableStub_orthogonal
      planar entry color
  have clauseStubOrthogonal :
      OrthogonalPolyline
        (occurrenceRibbonClauseStub
          planar entry color) := by
    exact occurrenceRibbonClauseStub_orthogonal
      planar entry color
  have firstOrthogonal :=
    variableStubOrthogonal.joinAtEndpoint
      (occurrenceRibbonCorridorCore_orthogonal
        presentation entry color)
      variableEndpoints.2
      coreEndpoints.1
  apply firstOrthogonal.joinAtEndpoint clauseStubOrthogonal
  · apply joinAtEndpoint_getLast?
    · exact variableEndpoints.2
    · exact coreEndpoints.1
    · exact coreEndpoints.2
  · exact clauseEndpoints.1

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
