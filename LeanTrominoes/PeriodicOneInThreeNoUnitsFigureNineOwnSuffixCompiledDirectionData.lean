/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineExtendedDirectionCompiler
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineFarTailDirectionData

/-!
# Compiled direction form of one inherited Figure 9 suffix

The normalized suffix is now expressed entirely at the stream boundary: one
finite fan/slot block followed by factor-`144` repetition of the original
source route after its first vertex.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open Gadget PeriodicOrthocrossing

/-- Exact source-emitter form of an inherited normalized suffix. -/
theorem normalizedFanInheritedRouteSuffix_compiledDirectionWord
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
    unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (fanInheritedRouteSuffix
            outputPlacement sourcePlacement sourceClause generatedClause
            data slot
            (AxisDirection.unitSubdividePolyline
              (scalePolyline 2 (first :: second :: rest))))) =
      normalizedExtendedDirectionBlock ⟨data, slot⟩ ++
        repeatDirections 144
          (unitSubdivisionDirections (second :: rest)) := by
  let origin := normalizedSourceClausePosition
    outputPlacement sourceClause generatedClause
  let farTail :=
    translatePolyline
      (inheritedSourceRouteShift
        outputPlacement sourcePlacement sourceClause generatedClause)
      (scalePolyline composedGadgetScale
        (AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (second :: rest))))
  rw [normalizedFanInheritedRouteSuffix_directionWord
    outputPlacement sourcePlacement sourceClause generatedClause
    data slot first second rest fanValid slotActive firstUnit
    scaledHead directionEq sourceOrthogonal sourceSimple]
  rw [show unitSubdivisionDirections
      (AxisDirection.normalizeOrthogonalPolyline
        (data.translatedExtendedRoute origin slot)) =
        normalizedExtendedDirectionBlock ⟨data, slot⟩ by
    exact normalizedTranslatedExtendedRoute_directionWord
      origin data fanValid slot slotActive]
  rw [show unitSubdivisionDirections farTail =
      repeatDirections 144
        (unitSubdivisionDirections (second :: rest)) by
    exact farTail_directionWord
      outputPlacement sourcePlacement sourceClause generatedClause
      first second rest sourceOrthogonal]

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
