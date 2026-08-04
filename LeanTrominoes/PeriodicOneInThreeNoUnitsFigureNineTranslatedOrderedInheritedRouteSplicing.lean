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

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
