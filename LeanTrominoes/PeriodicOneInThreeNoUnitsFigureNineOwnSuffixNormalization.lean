/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOwnTailSeparation

/-!
# Localized normalization of one inherited Figure 9 suffix

The only loops in an inherited Figure 9 suffix lie in its fixed extended
connector.  The simple inherited far tail meets that connector only at the
outer boundary, so the general endpoint-join localization theorem normalizes
the finite prefix and reattaches the unit-subdivided tail unchanged.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PeriodicOrthocrossing

/-- Normalize only the finite extended connector of an inherited suffix. -/
theorem normalizeOrthogonalPolyline_fanInheritedRouteSuffix
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
    (fanValid : data.IsValid)
    (slotActive : data.SlotActive slot)
    (firstUnit : AxisDirection.IsUnitAxisStep first second)
    (scaledHead :
      Cell.scale 2 first =
        PositionedPeriodicCNF.canonicalClausePosition
          sourcePlacement sourceClause)
    (directionEq :
      data.direction slot = AxisDirection.between first second)
    (sourceOrthogonal :
      OrthogonalPolyline (first :: second :: rest))
    (sourceSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (first :: second :: rest)) :
    let origin := normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause
    let farTail :=
      translatePolyline
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement sourceClause generatedClause)
        (scalePolyline composedGadgetScale
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (second :: rest))))
    AxisDirection.normalizeOrthogonalPolyline
        (fanInheritedRouteSuffix
          outputPlacement sourcePlacement sourceClause generatedClause
          data slot
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (first :: second :: rest)))) =
      joinAtEndpoint
        (AxisDirection.normalizeOrthogonalPolyline
          (data.translatedExtendedRoute origin slot))
        (AxisDirection.unitSubdividePolyline farTail) := by
  dsimp only
  let origin := normalizedSourceClausePosition
    outputPlacement sourceClause generatedClause
  let shift := inheritedSourceRouteShift
    outputPlacement sourcePlacement sourceClause generatedClause
  let extended := data.translatedExtendedRoute origin slot
  let farTail :=
    translatePolyline shift
      (scalePolyline composedGadgetScale
        (AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (second :: rest))))
  let boundary := Cell.add origin
    (ComposedClauseExitFanData.outerSourceExit
      (data.direction slot))
  have extendedNonempty : extended ≠ [] := by
    intro empty
    have extendedHead :=
      data.translatedExtendedRoute_head? origin fanValid slot slotActive
    simp [extended, empty] at extendedHead
  have extendedOrthogonal : OrthogonalPolyline extended :=
    data.translatedExtendedRoute_orthogonal
      origin fanValid slot slotActive
  have farTailOrthogonal : OrthogonalPolyline farTail := by
    have sourceTailOrthogonal : OrthogonalPolyline (second :: rest) :=
      (List.isChain_cons_cons.mp sourceOrthogonal).2
    exact
      ((AxisDirection.unitSubdividePolyline_orthogonal
          (sourceTailOrthogonal.scalePolyline (by norm_num))).scalePolyline
        (by
          norm_num [composedGadgetScale, PlanarOneInThree.gadgetScale,
            PeriodicOneInThreeNoUnitsPositioned.gadgetScale])).translate shift
  have farTailSimple :
      LocalIncidenceDrawing.RouteIsSimple farTail := by
    simpa only [farTail, shift] using
      farTail_isSimple
        outputPlacement sourcePlacement sourceClause generatedClause
        first second rest sourceOrthogonal sourceSimple
  have extendedLast : extended.getLast? = some boundary := by
    simpa only [extended, boundary] using
      data.translatedExtendedRoute_getLast?
        origin fanValid slot slotActive
  have farTailHead : farTail.head? = some boundary := by
    simpa only [farTail, boundary, origin, shift] using
      translatedScaledDoubledSubdividedTail_head?
        outputPlacement sourcePlacement sourceClause generatedClause
        data slot first second rest firstUnit scaledHead directionEq
  have farTailNonempty : farTail ≠ [] := by
    intro empty
    simp [empty] at farTailHead
  have onlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline extended →
        point ∈ AxisDirection.unitSubdividePolyline farTail →
        point = boundary := by
    simpa only [extended, farTail, boundary, origin, shift] using
      translatedExtendedRoute_farTail_onlyCommon
        outputPlacement sourcePlacement sourceClause generatedClause
        data slot first second rest fanValid slotActive firstUnit
        scaledHead directionEq sourceOrthogonal sourceSimple
  rw [fanInheritedRouteSuffix_eq_extended_join_farTail
    outputPlacement sourcePlacement sourceClause generatedClause
    data slot first second rest firstUnit scaledHead directionEq]
  exact
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_of_only_common
      extendedNonempty farTailNonempty extendedOrthogonal
      farTailOrthogonal farTailSimple extendedLast farTailHead onlyCommon

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
