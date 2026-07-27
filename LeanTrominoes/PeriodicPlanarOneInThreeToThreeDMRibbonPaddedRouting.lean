import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonRoutingBounds
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRouteBounds
import LeanTrominoes.PositionedPeriodicCNFRibbonScaling

/-!
# Padded normalized ribbon routing

The expanded finite checker uses an open one-cell halo, whereas a closed
ribbon macrocell may reach the next refined lattice line.  This file doubles
the ribbon-ready source before anchor normalization and ribbon refinement.
The doubled source has the one-unit upper margin proved by the scaling layer.

Pointwise bounds for corrected occurrence routes combine with the unchanged
finite gadget prefixes and clause routes to bound every assembled route, and
hence both endpoints of every stored segment.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

/-- The final corrected routing first doubles the source drawing, then
anchor-normalizes and performs the `128`-fold ribbon refinement. -/
noncomputable def paddedNormalizedRibbonThreeStrandRouting
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    ThreeStrandRouting
      (normalizedPositionedSource
        (source.scale 2) (placement.scale 2)).erase :=
  normalizedRibbonThreeStrandRouting presentation.scaleTwo

/-- Every point of every padded normalized corrected occurrence route lies
in the assembled open halo. -/
theorem paddedNormalizedRibbonRoute_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry :
      ActiveOccurrenceEntry
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase)
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈
        (paddedNormalizedRibbonThreeStrandRouting presentation).route
          entry color) :
    (assembledDrawing
      (paddedNormalizedRibbonThreeStrandRouting presentation))
      |>.PositionInExpandedSquare point := by
  let padded := presentation.scaleTwo
  let normalized :=
    normalizedRibbonReadyIncidencePresentation padded
  change
    point ∈ occurrenceRibbonThreeStrandRoute
      normalized.toPlanarIncidencePresentation entry color
    at pointMember
  change
    (assembledDrawing
      (ribbonThreeStrandRouting
        normalized.toContinuousPlanarIncidencePresentation))
      |>.PositionInExpandedSquare point
  apply occurrenceRibbonThreeStrandRoute_pointsInsideExpandedSquare
    normalized.toContinuousPlanarIncidencePresentation
    ?_ entry color pointMember
  exact
    padded.toPlanarIncidencePresentation
      |>.rebasedRoutePointsInExpandedSquareWithUpperMargin_anchorNormalize
        presentation.scaleTwo_rebasedRoutePointsInExpandedSquareWithUpperMargin

/-- Every point of an assembled typed incidence route is halo-bounded when
the corrected routing's source carries the upper-margin certificate. -/
theorem ribbonAssembledTypedIncidenceRoute_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (sourceBounds :
      presentation.toPlanarIncidencePresentation
        |>.RebasedRoutePointsInExpandedSquareWithUpperMargin)
    (triple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ assembledTypedIncidenceRoute
        (ribbonThreeStrandRouting presentation)
        triple color) :
    (assembledDrawing
      (ribbonThreeStrandRouting presentation))
      |>.PositionInExpandedSquare point := by
  let planar := presentation.toPlanarIncidencePresentation
  unfold assembledTypedIncidenceRoute at pointMember
  split at pointMember
  next atom slot variant localTriple tripleEq =>
    let member :
        Triple.ordinary atom slot variant localTriple ∈
          triples source.erase :=
      tripleEq ▸ triple.2
    let location :=
      ordinaryTriple_location source.erase atom slot variant
        localTriple member
    split at pointMember
    next routed =>
      let entry : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff
            source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      rcases mem_joinAtEndpoint pointMember with
        prefixMember | corridorMember
      · exact PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
          (standardAssembledOrdinaryPrefix_pointsInsideFundamentalSquare
            planar anchorsZero atom slot variant localTriple
            member color prefixMember)
      · apply occurrenceRibbonThreeStrandRoute_pointsInsideExpandedSquare
          presentation sourceBounds entry color
        simpa [ribbonThreeStrandRouting] using corridorMember
    next notRouted =>
      exact PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
        (standardAssembledOrdinaryPrefix_pointsInsideFundamentalSquare
          planar anchorsZero atom slot variant localTriple
          member color pointMember)
  next atom slot localTriple tripleEq =>
    let member :
        Triple.fixedRed atom slot localTriple ∈
          triples source.erase :=
      tripleEq ▸ triple.2
    let location :=
      fixedRedTriple_location source.erase atom slot localTriple member
    split at pointMember
    next routed =>
      let entry : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff
            source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      rcases mem_joinAtEndpoint pointMember with
        prefixMember | corridorMember
      · exact PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
          (standardAssembledFixedRedPrefix_pointsInsideFundamentalSquare
            planar anchorsZero atom slot localTriple
            member color prefixMember)
      · apply occurrenceRibbonThreeStrandRoute_pointsInsideExpandedSquare
          presentation sourceBounds entry color
        simpa [ribbonThreeStrandRouting] using corridorMember
    next notRouted =>
      exact PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
        (standardAssembledFixedRedPrefix_pointsInsideFundamentalSquare
          planar anchorsZero atom slot localTriple
          member color pointMember)
  next clauseIndex set tripleEq =>
    have member :
        Triple.clause (Variable := Variable) clauseIndex set ∈
          triples source.erase :=
      tripleEq ▸ triple.2
    have declared :=
      tripleMacrocellOwner_declared source.erase
        (.clause clauseIndex set) member
    have indexLt : clauseIndex < source.clauses.length := by
      simpa [tripleMacrocellOwner,
        AssemblyMacrocellOwner.IsDeclared,
        PositionedPeriodicCNF.erase] using declared
    exact PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
      (standardAssembledClauseRoute_pointsInsideFundamentalSquare
        planar anchorsZero clauseIndex indexLt set color
        pointMember)

/-- Total tag selection preserves the corrected assembled route bound,
including its unreachable empty fallback. -/
theorem ribbonAssembledRouteAtTag_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (sourceBounds :
      presentation.toPlanarIncidencePresentation
        |>.RebasedRoutePointsInExpandedSquareWithUpperMargin)
    (tag : PeriodicThreeDM.IncidenceTag)
    {point : Cell}
    (pointMember :
      point ∈ assembledRouteAtTag
        (ribbonThreeStrandRouting presentation) tag) :
    (assembledDrawing
      (ribbonThreeStrandRouting presentation))
      |>.PositionInExpandedSquare point := by
  unfold assembledRouteAtTag at pointMember
  split at pointMember
  next indexLt =>
    exact
      ribbonAssembledTypedIncidenceRoute_pointsInsideExpandedSquare
        presentation anchorsZero sourceBounds
        ⟨(triples source.erase)[tag.tripleIndex]'indexLt,
          List.getElem_mem indexLt⟩
        tag.color pointMember
  next indexNotLt =>
    simp at pointMember

/-- The complete corrected assembled route list is pointwise halo-bounded. -/
theorem ribbonAssembledRoutePointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (sourceBounds :
      presentation.toPlanarIncidencePresentation
        |>.RebasedRoutePointsInExpandedSquareWithUpperMargin) :
    (assembledDrawing
      (ribbonThreeStrandRouting presentation))
      |>.RoutePointsInExpandedSquare := by
  intro route routeMember point pointMember
  change route ∈
    assembledEdgeRoutes (ribbonThreeStrandRouting presentation)
    at routeMember
  unfold assembledEdgeRoutes at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨tag, tagMember, routeEq⟩
  subst route
  exact
    ribbonAssembledRouteAtTag_pointsInsideExpandedSquare
      presentation anchorsZero sourceBounds tag pointMember

/-- All stored segment endpoints of an upper-margin corrected assembly lie
in the open one-cell halo. -/
theorem ribbonAssembledSegmentEndpointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (sourceBounds :
      presentation.toPlanarIncidencePresentation
        |>.RebasedRoutePointsInExpandedSquareWithUpperMargin) :
    (assembledDrawing
      (ribbonThreeStrandRouting presentation))
      |>.SegmentEndpointsInExpandedSquare :=
  PeriodicGridDrawing.segmentEndpointsInExpandedSquare_of_routePoints
    (ribbonAssembledRoutePointsInExpandedSquare
      presentation anchorsZero sourceBounds)

/-- Doubling supplies the upper margin automatically, so every segment
endpoint of the final padded normalized ribbon assembly is halo-bounded. -/
theorem paddedNormalizedRibbonAssembledSegmentEndpointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    (assembledDrawing
      (paddedNormalizedRibbonThreeStrandRouting presentation))
      |>.SegmentEndpointsInExpandedSquare := by
  let padded := presentation.scaleTwo
  let normalized :=
    normalizedRibbonReadyIncidencePresentation padded
  change
    (assembledDrawing
      (ribbonThreeStrandRouting
        normalized.toContinuousPlanarIncidencePresentation))
      |>.SegmentEndpointsInExpandedSquare
  exact
    ribbonAssembledSegmentEndpointsInExpandedSquare
      normalized.toContinuousPlanarIncidencePresentation
      (normalizedPositionedSource_hasZeroClauseAnchors
        (source.scale 2) (placement.scale 2))
      (padded.toPlanarIncidencePresentation
        |>.rebasedRoutePointsInExpandedSquareWithUpperMargin_anchorNormalize
          presentation.scaleTwo_rebasedRoutePointsInExpandedSquareWithUpperMargin)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
