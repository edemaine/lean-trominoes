/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteSplicing
import LeanTrominoes.RetainedRayRasterizationTranslation

/-!
# Translated ordered Figure 9 inherited suffix assembly

Relative route separation compares one stored route with a period translate
of another.  The ordered Figure 9 suffix already decomposes into its extended
finite connector and refined far source tail.  This file records that the
same decomposition and strict-separation assembly commute with an arbitrary
additional translation.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Translating an ordered inherited suffix translates both its extended
connector and its refined far tail. -/
theorem translate_fanInheritedRouteSuffix_eq_extended_join_farTail
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (first second : Cell)
    (rest : List Cell)
    (offset : Cell)
    (firstUnit : AxisDirection.IsUnitAxisStep first second)
    (scaledHead :
      Cell.scale 2 first =
        PositionedPeriodicCNF.canonicalClausePosition
          sourcePlacement sourceClause)
    (directionEq :
      data.direction slot = AxisDirection.between first second) :
    PeriodicOrthocrossing.translatePolyline offset
        (fanInheritedRouteSuffix
          outputPlacement sourcePlacement sourceClause generatedClause
          data slot
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (first :: second :: rest)))) =
      joinAtEndpoint
        (PeriodicOrthocrossing.translatePolyline offset
          (data.translatedExtendedRoute
            (normalizedSourceClausePosition
              outputPlacement sourceClause generatedClause)
            slot))
        (PeriodicOrthocrossing.translatePolyline offset
          (PeriodicOrthocrossing.translatePolyline
            (inheritedSourceRouteShift
              outputPlacement sourcePlacement sourceClause generatedClause)
            (scalePolyline composedGadgetScale
              (AxisDirection.unitSubdividePolyline
                (scalePolyline 2 (second :: rest)))))) := by
  rw [fanInheritedRouteSuffix_eq_extended_join_farTail
    outputPlacement sourcePlacement sourceClause generatedClause
    data slot first second rest firstUnit scaledHead directionEq]
  exact translatePolyline_joinAtEndpoint _ _ _

/-- Strict separation from the translated extended connector and translated
far tail assembles into strict separation from the translated inherited
suffix. -/
theorem
    strictlyAvoids_translated_fanInheritedRouteSuffix_of_extended_of_farTail
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (first second : Cell)
    (rest localRoute : List Cell)
    (offset : Cell)
    (fanValid : data.IsValid)
    (slotActive : data.SlotActive slot)
    (firstUnit : AxisDirection.IsUnitAxisStep first second)
    (scaledHead :
      Cell.scale 2 first =
        PositionedPeriodicCNF.canonicalClausePosition
          sourcePlacement sourceClause)
    (directionEq :
      data.direction slot = AxisDirection.between first second)
    (extendedAvoid :
      RoutesStrictlyAvoidEachOther localRoute
        (PeriodicOrthocrossing.translatePolyline offset
          (data.translatedExtendedRoute
            (normalizedSourceClausePosition
              outputPlacement sourceClause generatedClause)
            slot)))
    (farTailAvoid :
      RoutesStrictlyAvoidEachOther localRoute
        (PeriodicOrthocrossing.translatePolyline offset
          (PeriodicOrthocrossing.translatePolyline
            (inheritedSourceRouteShift
              outputPlacement sourcePlacement sourceClause generatedClause)
            (scalePolyline composedGadgetScale
              (AxisDirection.unitSubdividePolyline
                (scalePolyline 2 (second :: rest))))))) :
    RoutesStrictlyAvoidEachOther localRoute
      (PeriodicOrthocrossing.translatePolyline offset
        (fanInheritedRouteSuffix
          outputPlacement sourcePlacement sourceClause generatedClause
          data slot
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (first :: second :: rest))))) := by
  rw [translate_fanInheritedRouteSuffix_eq_extended_join_farTail
    outputPlacement sourcePlacement sourceClause generatedClause
    data slot first second rest offset firstUnit scaledHead directionEq]
  let boundary :=
    Cell.add offset
      (Cell.add
        (normalizedSourceClausePosition
          outputPlacement sourceClause generatedClause)
        (ComposedClauseExitFanData.outerSourceExit
          (data.direction slot)))
  have extendedLastBase :=
    data.translatedExtendedRoute_getLast?
      (normalizedSourceClausePosition
        outputPlacement sourceClause generatedClause)
      fanValid slot slotActive
  have extendedLast :
      (PeriodicOrthocrossing.translatePolyline offset
        (data.translatedExtendedRoute
          (normalizedSourceClausePosition
            outputPlacement sourceClause generatedClause)
          slot)).getLast? = some boundary := by
    simpa [PeriodicOrthocrossing.translatePolyline, boundary] using
      congrArg (Option.map (Cell.add offset)) extendedLastBase
  have farHeadBase :=
    translatedScaledDoubledSubdividedTail_head?
      outputPlacement sourcePlacement sourceClause generatedClause
      data slot first second rest firstUnit scaledHead directionEq
  have farHead :
      (PeriodicOrthocrossing.translatePolyline offset
        (PeriodicOrthocrossing.translatePolyline
          (inheritedSourceRouteShift
            outputPlacement sourcePlacement sourceClause generatedClause)
          (scalePolyline composedGadgetScale
            (AxisDirection.unitSubdividePolyline
              (scalePolyline 2 (second :: rest)))))).head? =
        some boundary := by
    simpa [PeriodicOrthocrossing.translatePolyline, boundary] using
      congrArg (Option.map (Cell.add offset)) farHeadBase
  exact
    extendedAvoid.join_right farTailAvoid extendedLast farHead

/-- Strict separation from a translated fan-spliced inherited suffix also
holds for the translated transformed source tail contained in that suffix. -/
theorem
    strictlyAvoids_translatedInheritedSourceRouteTail_of_fanInheritedRouteSuffix
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (sourceRoute localRoute : List Cell)
    (offset : Cell)
    (fanValid : data.IsValid)
    (slotActive : data.SlotActive slot)
    (directionEq :
      data.direction slot =
        AxisDirection.polylineFirstDirection sourceRoute)
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause))
    (sourceTailNonempty :
      ∃ sourceExit, sourceRoute.tail.head? = some sourceExit)
    (sourceUnitSteps :
      sourceRoute.IsChain AxisDirection.IsUnitAxisStep)
    (strictSuffix :
      RoutesStrictlyAvoidEachOther localRoute
        (PeriodicOrthocrossing.translatePolyline offset
          (fanInheritedRouteSuffix
            outputPlacement sourcePlacement sourceClause generatedClause
            data slot sourceRoute))) :
    RoutesStrictlyAvoidEachOther localRoute
      (PeriodicOrthocrossing.translatePolyline offset
        ((inheritedSourceRoute
          outputPlacement sourcePlacement sourceClause generatedClause
          sourceRoute).tail)) := by
  let origin :=
    normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute
  let splicePoint :=
    Cell.add offset
      (Cell.add origin
        (ComposedClauseExitFanData.sourceExit
          (data.direction slot)))
  have connectorLastBase :=
    data.translatedRoute_getLast?
      origin fanValid slot slotActive
  have transformedTailHeadBase :=
    inheritedSourceRoute_tail_head?_of_unitSteps
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute sourceHead sourceTailNonempty sourceUnitSteps
  have connectorLast :
      (PeriodicOrthocrossing.translatePolyline offset
        (data.translatedRoute origin slot)).getLast? =
          some splicePoint := by
    simpa [PeriodicOrthocrossing.translatePolyline, splicePoint] using
      congrArg (Option.map (Cell.add offset)) connectorLastBase
  have transformedTailHead :
      (PeriodicOrthocrossing.translatePolyline offset transformed.tail).head? =
        some splicePoint := by
    simpa [PeriodicOrthocrossing.translatePolyline, splicePoint,
      transformed, origin, directionEq] using
      congrArg (Option.map (Cell.add offset)) transformedTailHeadBase
  unfold fanInheritedRouteSuffix replacePolylineHead at strictSuffix
  rw [translatePolyline_joinAtEndpoint] at strictSuffix
  exact (strictSuffix.of_join_right connectorLast transformedTailHead).2

/-- Version of
`strictlyAvoids_translatedInheritedSourceRouteTail_of_fanInheritedRouteSuffix`
where the fan suffix has already been rewritten to an equal presentation of
the source route. -/
theorem
    strictlyAvoids_translatedInheritedSourceRouteTail_of_fanInheritedRouteSuffix_of_sourceRoute_eq
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (sourceRoute fanSourceRoute localRoute : List Cell)
    (offset : Cell)
    (sourceRouteEq : sourceRoute = fanSourceRoute)
    (fanValid : data.IsValid)
    (slotActive : data.SlotActive slot)
    (directionEq :
      data.direction slot =
        AxisDirection.polylineFirstDirection sourceRoute)
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause))
    (sourceTailNonempty :
      ∃ sourceExit, sourceRoute.tail.head? = some sourceExit)
    (sourceUnitSteps :
      sourceRoute.IsChain AxisDirection.IsUnitAxisStep)
    (strictSuffix :
      RoutesStrictlyAvoidEachOther localRoute
        (PeriodicOrthocrossing.translatePolyline offset
          (fanInheritedRouteSuffix
            outputPlacement sourcePlacement sourceClause generatedClause
            data slot fanSourceRoute))) :
    RoutesStrictlyAvoidEachOther localRoute
      (PeriodicOrthocrossing.translatePolyline offset
        ((inheritedSourceRoute
          outputPlacement sourcePlacement sourceClause generatedClause
          sourceRoute).tail)) := by
  subst fanSourceRoute
  exact
    strictlyAvoids_translatedInheritedSourceRouteTail_of_fanInheritedRouteSuffix
      outputPlacement sourcePlacement sourceClause generatedClause data slot
      sourceRoute localRoute offset fanValid slotActive directionEq sourceHead
      sourceTailNonempty sourceUnitSteps strictSuffix

/-- Transport strict separation from a translated fan-spliced suffix across
an equality between two presentations of its source route. -/
theorem strictlyAvoids_translatedFanInheritedRouteSuffix_of_sourceRoute_eq
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (sourceRoute fanSourceRoute localRoute : List Cell)
    (offset : Cell)
    (sourceRouteEq : sourceRoute = fanSourceRoute)
    (strictSuffix :
      RoutesStrictlyAvoidEachOther localRoute
        (PeriodicOrthocrossing.translatePolyline offset
          (fanInheritedRouteSuffix
            outputPlacement sourcePlacement sourceClause generatedClause
            data slot fanSourceRoute))) :
    RoutesStrictlyAvoidEachOther localRoute
      (PeriodicOrthocrossing.translatePolyline offset
        (fanInheritedRouteSuffix
          outputPlacement sourcePlacement sourceClause generatedClause
          data slot sourceRoute)) := by
  subst fanSourceRoute
  exact strictSuffix

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
