import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorBounds

/-!
# Coordinated ribbon endpoint-fan systems

The ribbon corridor construction determines three colored boundary points at
each end of every source incidence route.  Connecting those points to the
finite variable and clause gadget ports is not merely a pointwise endpoint
problem: the three fans at a vertex must respect the cyclic order inherited
from the source embedding.

This file records a coordinated choice of all endpoint fans as explicit
geometric data.  It deliberately does not claim that the earlier independent
one-bend candidates always satisfy the contract.  Once a concrete source
construction supplies compatible fans, the definitions below assemble them
with the already certified corridor cores and package the result as a
`ThreeStrandRouting`.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing

/-- A coordinated selection of variable- and clause-side ribbon fans.

Besides exact endpoints and rectilinearity, every fan is required to remain
inside the refined macrocell of its source endpoint.  Global pairwise
separation is intentionally a separate certificate, because it relates fans
belonging to different occurrences. -/
structure RibbonEndpointFanSystem
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement) where
  variableStub :
    ActiveOccurrenceEntry source.erase → WireColor → List Cell
  clauseStub :
    ActiveOccurrenceEntry source.erase → WireColor → List Cell
  variableStubEndpoints :
    ∀ entry color,
      (variableStub entry color).head? =
          some (Cell.add
            (constructedVariableOrigin placement
              standardThreeStrandLayout entry.1.1)
            (routedVariablePortPosition source.erase entry color)) ∧
        (variableStub entry color).getLast? =
          some (ribbonCorridorRouteStart color
            (occurrenceUnitSourceRoute presentation entry))
  clauseStubEndpoints :
    ∀ entry color,
      (clauseStub entry color).head? =
          some (ribbonCorridorRouteEnd color
            (occurrenceUnitSourceRoute presentation entry)) ∧
        (clauseStub entry color).getLast? =
          some (routedClauseTargetPosition source.erase
            (standardThreeStrandLayout.factor * placement.period)
            (constructedClauseOrigin source standardThreeStrandLayout)
            entry color)
  variableStubOrthogonal :
    ∀ entry color, OrthogonalPolyline (variableStub entry color)
  clauseStubOrthogonal :
    ∀ entry color, OrthogonalPolyline (clauseStub entry color)
  variableStubPointsBounded :
    ∀ entry color {point},
      point ∈ variableStub entry color →
        InRibbonMacrocell (placement.position entry.1.1) point
  clauseStubPointsBounded :
    ∀ entry color {point},
      point ∈ clauseStub entry color →
        let data := occurrenceSpliceData presentation entry
        InRibbonMacrocell
          (PositionedPeriodicCNF.variableToClauseTarget
            placement data.positionedClause data.tagged.1)
          point

namespace RibbonEndpointFanSystem

/-- Complete colored route obtained from a coordinated endpoint-fan system
and the certified ribbon corridor core. -/
noncomputable def occurrenceThreeStrandRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {presentation : source.PlanarIncidencePresentation placement}
    (fans : RibbonEndpointFanSystem presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  joinAtEndpoint
    (joinAtEndpoint
      (fans.variableStub entry color)
      (occurrenceRibbonCorridorCore presentation entry color))
    (fans.clauseStub entry color)

/-- A coordinated route has the exact finite-gadget endpoints expected by
the typed 3DM assembly. -/
theorem occurrenceThreeStrandRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {presentation : source.PlanarIncidencePresentation placement}
    (fans : RibbonEndpointFanSystem presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (fans.occurrenceThreeStrandRoute entry color).head? =
        some (Cell.add
          (constructedVariableOrigin placement
            standardThreeStrandLayout entry.1.1)
          (routedVariablePortPosition source.erase entry color)) ∧
      (fans.occurrenceThreeStrandRoute entry color).getLast? =
        some (routedClauseTargetPosition source.erase
          (standardThreeStrandLayout.factor * placement.period)
          (constructedClauseOrigin source standardThreeStrandLayout)
          entry color) := by
  have coreEndpoints :=
    occurrenceRibbonCorridorCore_endpoints
      presentation entry color
  have variableEndpoints :=
    fans.variableStubEndpoints entry color
  have clauseEndpoints :=
    fans.clauseStubEndpoints entry color
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

/-- Joining a coordinated fan system to a continuously planar source
corridor preserves rectilinearity. -/
theorem occurrenceThreeStrandRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (fans : RibbonEndpointFanSystem
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    OrthogonalPolyline
      (fans.occurrenceThreeStrandRoute entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  have coreEndpoints :=
    occurrenceRibbonCorridorCore_endpoints
      planar entry color
  have variableEndpoints :=
    fans.variableStubEndpoints entry color
  have clauseEndpoints :=
    fans.clauseStubEndpoints entry color
  have firstOrthogonal :=
    (fans.variableStubOrthogonal entry color).joinAtEndpoint
      (occurrenceRibbonCorridorCore_orthogonal
        presentation entry color)
      variableEndpoints.2
      coreEndpoints.1
  apply firstOrthogonal.joinAtEndpoint
      (fans.clauseStubOrthogonal entry color)
  · apply joinAtEndpoint_getLast?
    · exact variableEndpoints.2
    · exact coreEndpoints.1
    · exact coreEndpoints.2
  · exact clauseEndpoints.1

/-- A coordinated endpoint-fan system supplies the routing portion of the
planar exact-one-to-3DM construction. -/
noncomputable def threeStrandRouting
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (fans : RibbonEndpointFanSystem
      presentation.toPlanarIncidencePresentation) :
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
    fans.occurrenceThreeStrandRoute
  routeEndpoints :=
    fans.occurrenceThreeStrandRoute_endpoints
  routeOrthogonal :=
    fans.occurrenceThreeStrandRoute_orthogonal presentation

end RibbonEndpointFanSystem

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
