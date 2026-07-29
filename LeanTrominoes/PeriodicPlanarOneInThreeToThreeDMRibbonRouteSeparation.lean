import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonRouting
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCorridorSeparation

/-!
# Separation interface for complete corrected ribbon routes

The corridor cores are now unconditionally separated.  This file isolates
the remaining endpoint-fan geometry into five pairwise obligations and proves
that those obligations compose across both endpoint joins to separate the
complete corrected routes.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Two colored occurrence strands are distinct routing objects. -/
abbrev RibbonStrandsDifferent
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (first : ActiveOccurrenceEntry source)
    (firstColor : WireColor)
    (second : ActiveOccurrenceEntry source)
    (secondColor : WireColor) : Prop :=
  (first, firstColor) ≠ (second, secondColor)

/-- Corridor cores are strictly separated for any two distinct colored
strands, whether the distinction is the occurrence or just the color. -/
theorem occurrenceRibbonCorridorCores_strictlyAvoidEachOther_of_strands_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    {first second : ActiveOccurrenceEntry source.erase}
    {firstColor secondColor : WireColor}
    (different :
      RibbonStrandsDifferent
        first firstColor second secondColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation first firstColor)
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation second secondColor) := by
  by_cases occurrencesEqual : first = second
  · subst second
    have colorsDifferent : firstColor ≠ secondColor := by
      intro colorsEqual
      exact different (by simp [colorsEqual])
    exact
      occurrenceRibbonCorridorCores_strictlyAvoidEachOther
        presentation first colorsDifferent
  · exact
      occurrenceRibbonCorridorCores_strictlyAvoidEachOther_of_ne
        presentation occurrencesEqual firstColor secondColor

/-- The five endpoint-containing pair types not already covered by
core-versus-core separation.  Symmetry supplies the three reverse-order
types. -/
structure RibbonEndpointFanSeparation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    Prop where
  variableVariable :
    ∀ first firstColor second secondColor,
      RibbonStrandsDifferent
          first firstColor second secondColor →
        RoutesStrictlyAvoidEachOther
          (occurrenceRibbonVariableStub
            presentation.toPlanarIncidencePresentation
            first firstColor)
          (occurrenceRibbonVariableStub
            presentation.toPlanarIncidencePresentation
            second secondColor)
  variableCore :
    ∀ first firstColor second secondColor,
      RibbonStrandsDifferent
          first firstColor second secondColor →
        RoutesStrictlyAvoidEachOther
          (occurrenceRibbonVariableStub
            presentation.toPlanarIncidencePresentation
            first firstColor)
          (occurrenceRibbonCorridorCore
            presentation.toPlanarIncidencePresentation
            second secondColor)
  variableClause :
    ∀ first firstColor second secondColor,
      RibbonStrandsDifferent
          first firstColor second secondColor →
        RoutesStrictlyAvoidEachOther
          (occurrenceRibbonVariableStub
            presentation.toPlanarIncidencePresentation
            first firstColor)
          (occurrenceRibbonClauseStub
            presentation.toPlanarIncidencePresentation
            second secondColor)
  coreClause :
    ∀ first firstColor second secondColor,
      RibbonStrandsDifferent
          first firstColor second secondColor →
        RoutesStrictlyAvoidEachOther
          (occurrenceRibbonCorridorCore
            presentation.toPlanarIncidencePresentation
            first firstColor)
          (occurrenceRibbonClauseStub
            presentation.toPlanarIncidencePresentation
            second secondColor)
  clauseClause :
    ∀ first firstColor second secondColor,
      RibbonStrandsDifferent
          first firstColor second secondColor →
        RoutesStrictlyAvoidEachOther
          (occurrenceRibbonClauseStub
            presentation.toPlanarIncidencePresentation
            first firstColor)
          (occurrenceRibbonClauseStub
            presentation.toPlanarIncidencePresentation
            second secondColor)

namespace RibbonEndpointFanSeparation

/-- The five endpoint-fan obligations plus the proved core theorem separate
the two complete joined corrected routes. -/
theorem occurrenceRibbonThreeStrandRoutes_strictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement}
    (separation : RibbonEndpointFanSeparation presentation)
    {first second : ActiveOccurrenceEntry source.erase}
    {firstColor secondColor : WireColor}
    (different :
      RibbonStrandsDifferent
        first firstColor second secondColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceRibbonThreeStrandRoute
        presentation.toPlanarIncidencePresentation
        first firstColor)
      (occurrenceRibbonThreeStrandRoute
        presentation.toPlanarIncidencePresentation
        second secondColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  have reverseDifferent :
      RibbonStrandsDifferent
        second secondColor first firstColor :=
    Ne.symm different
  have firstVariableEndpoints :=
    occurrenceRibbonVariableStub_endpoints
      planar first firstColor
  have firstCoreEndpoints :=
    occurrenceRibbonCorridorCore_endpoints
      planar first firstColor
  have firstClauseEndpoints :=
    occurrenceRibbonClauseStub_endpoints
      planar first firstColor
  have secondVariableEndpoints :=
    occurrenceRibbonVariableStub_endpoints
      planar second secondColor
  have secondCoreEndpoints :=
    occurrenceRibbonCorridorCore_endpoints
      planar second secondColor
  have secondClauseEndpoints :=
    occurrenceRibbonClauseStub_endpoints
      planar second secondColor
  have firstPrefixLast :
      (joinAtEndpoint
        (occurrenceRibbonVariableStub
          planar first firstColor)
        (occurrenceRibbonCorridorCore
          planar first firstColor)).getLast? =
        some (ribbonCorridorRouteEnd
          (routedRibbonLane source.erase first firstColor)
          (occurrenceUnitSourceRoute planar first)) :=
    joinAtEndpoint_getLast?
      firstVariableEndpoints.2
      firstCoreEndpoints.1
      firstCoreEndpoints.2
  have secondPrefixLast :
      (joinAtEndpoint
        (occurrenceRibbonVariableStub
          planar second secondColor)
        (occurrenceRibbonCorridorCore
          planar second secondColor)).getLast? =
        some (ribbonCorridorRouteEnd
          (routedRibbonLane source.erase second secondColor)
          (occurrenceUnitSourceRoute planar second)) :=
    joinAtEndpoint_getLast?
      secondVariableEndpoints.2
      secondCoreEndpoints.1
      secondCoreEndpoints.2
  have firstFullAvoidsSecondVariable :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint
          (joinAtEndpoint
            (occurrenceRibbonVariableStub
              planar first firstColor)
            (occurrenceRibbonCorridorCore
              planar first firstColor))
          (occurrenceRibbonClauseStub
            planar first firstColor))
        (occurrenceRibbonVariableStub
          planar second secondColor) := by
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
            (occurrenceRibbonVariableStub
              planar first firstColor)
            (occurrenceRibbonCorridorCore
              planar first firstColor))
          (occurrenceRibbonClauseStub
            planar first firstColor))
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
            (occurrenceRibbonVariableStub
              planar first firstColor)
            (occurrenceRibbonCorridorCore
              planar first firstColor))
          (occurrenceRibbonClauseStub
            planar first firstColor))
        (occurrenceRibbonClauseStub
          planar second secondColor) := by
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
  simpa [occurrenceRibbonThreeStrandRoute, planar] using fullAvoid

end RibbonEndpointFanSeparation

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
