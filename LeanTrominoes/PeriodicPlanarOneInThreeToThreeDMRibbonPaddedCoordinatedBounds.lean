/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedCoordinatedRouting

/-!
# Halo bounds for the padded coordinated ribbon assembly

The coordinated endpoint fans satisfy the same macrocell-containment
contract as the independent fan candidates.  This lifts their pointwise
halo bounds through the finite 3DM prefixes and the assembled incidence-tag
enumeration.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

/-- Fundamental-square membership of an assembled position depends only on
the routing period, not on the route field. -/
private theorem assembledPositionInFundamentalSquare_of_period_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (first second : ThreeStrandRouting source)
    (periodEq : first.period = second.period)
    {point : Cell}
    (inside :
      (assembledDrawing first).PositionInFundamentalSquare point) :
    (assembledDrawing second).PositionInFundamentalSquare point := by
  simp only [PeriodicGridDrawing.PositionInFundamentalSquare] at inside ⊢
  rw [assembledDrawing_gridSize] at inside ⊢
  rw [← periodEq]
  exact inside

/-- Every point of an assembled typed incidence route using the final
coordinated endpoint fans lies in the open one-cell halo. -/
theorem paddedNormalizedCoordinatedAssembledTypedIncidenceRoute_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes)
    (triple :
      {triple : Triple Variable //
        triple ∈ triples
          (normalizedPositionedSource
            (source.scale 2) (placement.scale 2)).erase})
    (color : WireColor) {point : Cell}
    (pointMember :
      point ∈ assembledTypedIncidenceRoute
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered)
        triple color) :
    (assembledDrawing
      (paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered))
      |>.PositionInExpandedSquare point := by
  let normalized :=
    normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
  let compatible :=
    paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      presentation width occurrences arity variableOrdered clauseOrdered
  let routing :=
    paddedNormalizedCoordinatedRibbonThreeStrandRouting
      presentation width occurrences arity
      variableOrdered clauseOrdered
  have anchorsZero :
      HasZeroClauseAnchors
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)) :=
    normalizedPositionedSource_hasZeroClauseAnchors
      (source.scale 2) (placement.scale 2)
  unfold assembledTypedIncidenceRoute at pointMember
  split at pointMember
  next atom slot variant localTriple tripleEq =>
    let member :
        Triple.ordinary atom slot variant localTriple ∈
          triples
            (normalizedPositionedSource
              (source.scale 2) (placement.scale 2)).erase :=
      tripleEq ▸ triple.2
    let location :=
      ordinaryTriple_location
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase
        atom slot variant localTriple member
    split at pointMember
    next routed =>
      let entry :
          ActiveOccurrenceEntry
            (normalizedPositionedSource
              (source.scale 2) (placement.scale 2)).erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff _ atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      rcases mem_joinAtEndpoint pointMember with
        prefixMember | corridorMember
      · apply PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
        apply assembledPositionInFundamentalSquare_of_period_eq
          (constructedThreeStrandRouting
            normalized.toPlanarIncidencePresentation
            standardThreeStrandLayout)
          routing rfl
        exact
          standardAssembledOrdinaryPrefix_pointsInsideFundamentalSquare
            normalized.toPlanarIncidencePresentation anchorsZero
            atom slot variant localTriple member color prefixMember
      · exact
          paddedNormalizedCoordinatedRibbonRoute_pointsInsideExpandedSquare
            presentation width occurrences arity
            variableOrdered clauseOrdered entry color
            (by simpa [routing,
              paddedNormalizedCoordinatedRibbonThreeStrandRouting,
              coordinatedSourceRibbonThreeStrandRouting] using
                corridorMember)
    next notRouted =>
      apply PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
      apply assembledPositionInFundamentalSquare_of_period_eq
        (constructedThreeStrandRouting
          normalized.toPlanarIncidencePresentation
          standardThreeStrandLayout)
        routing rfl
      exact
        standardAssembledOrdinaryPrefix_pointsInsideFundamentalSquare
          normalized.toPlanarIncidencePresentation anchorsZero
          atom slot variant localTriple member color pointMember
  next atom slot localTriple tripleEq =>
    let member :
        Triple.fixedRed atom slot localTriple ∈
          triples
            (normalizedPositionedSource
              (source.scale 2) (placement.scale 2)).erase :=
      tripleEq ▸ triple.2
    let location :=
      fixedRedTriple_location
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase
        atom slot localTriple member
    split at pointMember
    next routed =>
      let entry :
          ActiveOccurrenceEntry
            (normalizedPositionedSource
              (source.scale 2) (placement.scale 2)).erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff _ atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      rcases mem_joinAtEndpoint pointMember with
        prefixMember | corridorMember
      · apply PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
        apply assembledPositionInFundamentalSquare_of_period_eq
          (constructedThreeStrandRouting
            normalized.toPlanarIncidencePresentation
            standardThreeStrandLayout)
          routing rfl
        exact
          standardAssembledFixedRedPrefix_pointsInsideFundamentalSquare
            normalized.toPlanarIncidencePresentation anchorsZero
            atom slot localTriple member color prefixMember
      · exact
          paddedNormalizedCoordinatedRibbonRoute_pointsInsideExpandedSquare
            presentation width occurrences arity
            variableOrdered clauseOrdered entry color
            (by simpa [routing,
              paddedNormalizedCoordinatedRibbonThreeStrandRouting,
              coordinatedSourceRibbonThreeStrandRouting] using
                corridorMember)
    next notRouted =>
      apply PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
      apply assembledPositionInFundamentalSquare_of_period_eq
        (constructedThreeStrandRouting
          normalized.toPlanarIncidencePresentation
          standardThreeStrandLayout)
        routing rfl
      exact
        standardAssembledFixedRedPrefix_pointsInsideFundamentalSquare
          normalized.toPlanarIncidencePresentation anchorsZero
          atom slot localTriple member color pointMember
  next clauseIndex set tripleEq =>
    have member :
        Triple.clause (Variable := Variable) clauseIndex set ∈
          triples
            (normalizedPositionedSource
              (source.scale 2) (placement.scale 2)).erase :=
      tripleEq ▸ triple.2
    have declared :=
      tripleMacrocellOwner_declared
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase
        (.clause clauseIndex set) member
    have indexLt :
        clauseIndex <
          (normalizedPositionedSource
            (source.scale 2) (placement.scale 2)).clauses.length := by
      simpa [tripleMacrocellOwner,
        AssemblyMacrocellOwner.IsDeclared,
        PositionedPeriodicCNF.erase] using declared
    apply PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
    apply assembledPositionInFundamentalSquare_of_period_eq
      (constructedThreeStrandRouting
        normalized.toPlanarIncidencePresentation
        standardThreeStrandLayout)
      routing rfl
    exact
      standardAssembledClauseRoute_pointsInsideFundamentalSquare
        normalized.toPlanarIncidencePresentation anchorsZero
        clauseIndex indexLt set color pointMember

/-- Every genuine incidence tag selects a halo-bounded route in the final
coordinated assembly. -/
theorem paddedNormalizedCoordinatedAssembledRouteAtTag_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes)
    (tag : PeriodicThreeDM.IncidenceTag) {point : Cell}
    (pointMember :
      point ∈ assembledRouteAtTag
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered) tag) :
    (assembledDrawing
      (paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered))
      |>.PositionInExpandedSquare point := by
  unfold assembledRouteAtTag at pointMember
  split at pointMember
  next indexLt =>
    exact
      paddedNormalizedCoordinatedAssembledTypedIncidenceRoute_pointsInsideExpandedSquare
        presentation width occurrences arity
        variableOrdered clauseOrdered
        ⟨(triples
          (normalizedPositionedSource
            (source.scale 2) (placement.scale 2)).erase)[tag.tripleIndex]'indexLt,
          List.getElem_mem indexLt⟩
        tag.color pointMember
  next indexNotLt =>
    simp at pointMember

/-- The complete stored route list of the final coordinated assembly is
pointwise halo-bounded. -/
theorem paddedNormalizedCoordinatedAssembledRoutePointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    (assembledDrawing
      (paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered))
      |>.RoutePointsInExpandedSquare := by
  intro route routeMember point pointMember
  change route ∈
    assembledEdgeRoutes
      (paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered)
    at routeMember
  unfold assembledEdgeRoutes at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨tag, tagMember, routeEq⟩
  subst route
  exact
    paddedNormalizedCoordinatedAssembledRouteAtTag_pointsInsideExpandedSquare
      presentation width occurrences arity
      variableOrdered clauseOrdered tag pointMember

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
