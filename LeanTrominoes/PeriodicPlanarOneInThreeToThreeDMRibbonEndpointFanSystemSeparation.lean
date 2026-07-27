import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFanSystem
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonRouteSeparation

/-!
# Separation of routes from a coordinated endpoint-fan system

Corridor cores belonging to distinct colored strands are already
unconditionally separated.  This file states the five remaining kinds of
endpoint-containing pair for an arbitrary coordinated fan system and proves
that they compose across both endpoint joins to separate its complete routes.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace RibbonEndpointFanSystem

/-- The five endpoint-containing pair types not covered by the generic
core-versus-core theorem.  Symmetry supplies the reverse-order cases. -/
structure Separation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (fans : RibbonEndpointFanSystem
      presentation.toPlanarIncidencePresentation) : Prop where
  variableVariable :
    ∀ first firstColor second secondColor,
      RibbonStrandsDifferent
          first firstColor second secondColor →
        RoutesStrictlyAvoidEachOther
          (fans.variableStub first firstColor)
          (fans.variableStub second secondColor)
  variableCore :
    ∀ first firstColor second secondColor,
      RibbonStrandsDifferent
          first firstColor second secondColor →
        RoutesStrictlyAvoidEachOther
          (fans.variableStub first firstColor)
          (occurrenceRibbonCorridorCore
            presentation.toPlanarIncidencePresentation
            second secondColor)
  variableClause :
    ∀ first firstColor second secondColor,
      RibbonStrandsDifferent
          first firstColor second secondColor →
        RoutesStrictlyAvoidEachOther
          (fans.variableStub first firstColor)
          (fans.clauseStub second secondColor)
  coreClause :
    ∀ first firstColor second secondColor,
      RibbonStrandsDifferent
          first firstColor second secondColor →
        RoutesStrictlyAvoidEachOther
          (occurrenceRibbonCorridorCore
            presentation.toPlanarIncidencePresentation
            first firstColor)
          (fans.clauseStub second secondColor)
  clauseClause :
    ∀ first firstColor second secondColor,
      RibbonStrandsDifferent
          first firstColor second secondColor →
        RoutesStrictlyAvoidEachOther
          (fans.clauseStub first firstColor)
          (fans.clauseStub second secondColor)

namespace Separation

/-- The fan-system obligations plus corridor-core separation imply strict
separation of any two distinct complete colored routes. -/
theorem occurrenceThreeStrandRoutes_strictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement}
    {fans : RibbonEndpointFanSystem
      presentation.toPlanarIncidencePresentation}
    (separation : Separation presentation fans)
    {first second : ActiveOccurrenceEntry source.erase}
    {firstColor secondColor : WireColor}
    (different :
      RibbonStrandsDifferent
        first firstColor second secondColor) :
    RoutesStrictlyAvoidEachOther
      (fans.occurrenceThreeStrandRoute first firstColor)
      (fans.occurrenceThreeStrandRoute second secondColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  have reverseDifferent :
      RibbonStrandsDifferent
        second secondColor first firstColor :=
    Ne.symm different
  have firstVariableEndpoints :=
    fans.variableStubEndpoints first firstColor
  have firstCoreEndpoints :=
    occurrenceRibbonCorridorCore_endpoints
      planar first firstColor
  have firstClauseEndpoints :=
    fans.clauseStubEndpoints first firstColor
  have secondVariableEndpoints :=
    fans.variableStubEndpoints second secondColor
  have secondCoreEndpoints :=
    occurrenceRibbonCorridorCore_endpoints
      planar second secondColor
  have secondClauseEndpoints :=
    fans.clauseStubEndpoints second secondColor
  have firstPrefixLast :
      (joinAtEndpoint
        (fans.variableStub first firstColor)
        (occurrenceRibbonCorridorCore
          planar first firstColor)).getLast? =
        some (ribbonCorridorRouteEnd firstColor
          (occurrenceUnitSourceRoute planar first)) :=
    joinAtEndpoint_getLast?
      firstVariableEndpoints.2
      firstCoreEndpoints.1
      firstCoreEndpoints.2
  have secondPrefixLast :
      (joinAtEndpoint
        (fans.variableStub second secondColor)
        (occurrenceRibbonCorridorCore
          planar second secondColor)).getLast? =
        some (ribbonCorridorRouteEnd secondColor
          (occurrenceUnitSourceRoute planar second)) :=
    joinAtEndpoint_getLast?
      secondVariableEndpoints.2
      secondCoreEndpoints.1
      secondCoreEndpoints.2
  have firstFullAvoidsSecondVariable :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint
          (joinAtEndpoint
            (fans.variableStub first firstColor)
            (occurrenceRibbonCorridorCore
              planar first firstColor))
          (fans.clauseStub first firstColor))
        (fans.variableStub second secondColor) := by
    have prefixAvoid :=
      (separation.variableVariable
        first firstColor second secondColor different).join_left
        ((separation.variableCore
          second secondColor first firstColor
          reverseDifferent).symm)
        firstVariableEndpoints.2 firstCoreEndpoints.1
    exact
      prefixAvoid.join_left
        ((separation.variableClause
          second secondColor first firstColor
          reverseDifferent).symm)
        firstPrefixLast firstClauseEndpoints.1
  have firstFullAvoidsSecondCore :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint
          (joinAtEndpoint
            (fans.variableStub first firstColor)
            (occurrenceRibbonCorridorCore
              planar first firstColor))
          (fans.clauseStub first firstColor))
        (occurrenceRibbonCorridorCore
          planar second secondColor) := by
    have prefixAvoid :=
      (separation.variableCore
        first firstColor second secondColor different).join_left
        (occurrenceRibbonCorridorCores_strictlyAvoidEachOther_of_strands_ne
          presentation different)
        firstVariableEndpoints.2 firstCoreEndpoints.1
    exact
      prefixAvoid.join_left
        ((separation.coreClause
          second secondColor first firstColor
          reverseDifferent).symm)
        firstPrefixLast firstClauseEndpoints.1
  have firstFullAvoidsSecondClause :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint
          (joinAtEndpoint
            (fans.variableStub first firstColor)
            (occurrenceRibbonCorridorCore
              planar first firstColor))
          (fans.clauseStub first firstColor))
        (fans.clauseStub second secondColor) := by
    have prefixAvoid :=
      (separation.variableClause
        first firstColor second secondColor different).join_left
        (separation.coreClause
          first firstColor second secondColor different)
        firstVariableEndpoints.2 firstCoreEndpoints.1
    exact
      prefixAvoid.join_left
        (separation.clauseClause
          first firstColor second secondColor different)
        firstPrefixLast firstClauseEndpoints.1
  have firstFullAvoidsSecondPrefix :=
    firstFullAvoidsSecondVariable.join_right
      firstFullAvoidsSecondCore
      secondVariableEndpoints.2 secondCoreEndpoints.1
  have fullAvoid :=
    firstFullAvoidsSecondPrefix.join_right
      firstFullAvoidsSecondClause
      secondPrefixLast secondClauseEndpoints.1
  simpa [occurrenceThreeStrandRoute, planar] using fullAvoid

end Separation

/-- The legacy five obligations for the independent one-bend candidates are
exactly a separation certificate for their packaged fan system. -/
def separationOfIndependentOneBend
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement}
    (separation : RibbonEndpointFanSeparation presentation) :
    Separation presentation
      (independentOneBendEndpointFanSystem
        presentation.toPlanarIncidencePresentation) where
  variableVariable :=
    separation.variableVariable
  variableCore :=
    separation.variableCore
  variableClause :=
    separation.variableClause
  coreClause :=
    separation.coreClause
  clauseClause :=
    separation.clauseClause

end RibbonEndpointFanSystem

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
