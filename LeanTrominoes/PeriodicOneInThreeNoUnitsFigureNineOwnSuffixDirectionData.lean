/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionNormalization
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionEndpointJoin
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOwnSuffixNormalization

/-!
# Direction word of one inherited Figure 9 suffix

Localized route normalization becomes a concatenation law at the direction
boundary: normalize the fixed extended connector, then emit the inherited
far-tail word unchanged.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PeriodicOrthocrossing
open Gadget

/-- The normalized inherited suffix direction word is a finite normalized
connector word followed by the unchanged far-tail direction word. -/
theorem normalizedFanInheritedRouteSuffix_directionWord
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
    let extended := data.translatedExtendedRoute origin slot
    let farTail :=
      translatePolyline
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement sourceClause generatedClause)
        (scalePolyline composedGadgetScale
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (second :: rest))))
    unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (fanInheritedRouteSuffix
            outputPlacement sourcePlacement sourceClause generatedClause
            data slot
            (AxisDirection.unitSubdividePolyline
              (scalePolyline 2 (first :: second :: rest))))) =
      unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline extended) ++
        unitSubdivisionDirections farTail := by
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
  have normalizedExtendedNonempty :
      AxisDirection.normalizeOrthogonalPolyline extended ≠ [] :=
    AxisDirection.normalizeOrthogonalPolyline_ne_nil
      extendedNonempty extendedOrthogonal
  have extendedLast : extended.getLast? = some boundary := by
    simpa only [extended, boundary] using
      data.translatedExtendedRoute_getLast?
        origin fanValid slot slotActive
  have normalizedExtendedLast :
      (AxisDirection.normalizeOrthogonalPolyline extended).getLast? =
        some boundary := by
    rw [AxisDirection.normalizeOrthogonalPolyline_getLast?
      extendedNonempty extendedOrthogonal, extendedLast]
  have farTailOrthogonal : OrthogonalPolyline farTail := by
    have sourceTailOrthogonal : OrthogonalPolyline (second :: rest) :=
      (List.isChain_cons_cons.mp sourceOrthogonal).2
    exact
      ((AxisDirection.unitSubdividePolyline_orthogonal
          (sourceTailOrthogonal.scalePolyline (by norm_num))).scalePolyline
        (by
          norm_num [composedGadgetScale, PlanarOneInThree.gadgetScale,
            PeriodicOneInThreeNoUnitsPositioned.gadgetScale])).translate shift
  have farTailHead : farTail.head? = some boundary := by
    simpa only [farTail, boundary, origin, shift] using
      translatedScaledDoubledSubdividedTail_head?
        outputPlacement sourcePlacement sourceClause generatedClause
        data slot first second rest firstUnit scaledHead directionEq
  have farTailNonempty : farTail ≠ [] := by
    intro empty
    simp [empty] at farTailHead
  have subdividedFarTailHead :
      (AxisDirection.unitSubdividePolyline farTail).head? =
        some boundary := by
    rw [AxisDirection.unitSubdividePolyline_head?
      farTailNonempty, farTailHead]
  rw [normalizeOrthogonalPolyline_fanInheritedRouteSuffix
    outputPlacement sourcePlacement sourceClause generatedClause
    data slot first second rest fanValid slotActive firstUnit
    scaledHead directionEq sourceOrthogonal sourceSimple]
  rw [unitSubdivisionDirections_joinAtEndpoint
    normalizedExtendedNonempty
    (normalizedExtendedLast.trans subdividedFarTailHead.symm)]
  rw [unitSubdivisionDirections_unitSubdividePolyline
    farTail farTailOrthogonal]

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
