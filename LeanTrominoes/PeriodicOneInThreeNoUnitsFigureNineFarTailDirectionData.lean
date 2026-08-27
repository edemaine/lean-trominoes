/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionScalingCompiler
import LeanTrominoes.GadgetSparseRouteDirectionNormalization
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOwnSuffixDirectionData

/-!
# Direction word of the inherited Figure 9 far tail

The far tail applies factor-two source clearance, ordered subdivision,
factor-`72` gadget scaling, and translation.  At the direction boundary these
collapse to factor-`144` repetition of the original source tail word.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open Gadget PeriodicOrthocrossing

/-- The complete transformed far-tail word is the original source-tail word
with every direction repeated `144` times. -/
theorem farTail_directionWord
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
    (first second : Cell)
    (rest : List Cell)
    (sourceOrthogonal :
      OrthogonalPolyline (first :: second :: rest)) :
    unitSubdivisionDirections
        (translatePolyline
          (inheritedSourceRouteShift
            outputPlacement sourcePlacement sourceClause generatedClause)
          (scalePolyline composedGadgetScale
            (AxisDirection.unitSubdividePolyline
              (scalePolyline 2 (second :: rest))))) =
      repeatDirections 144
        (unitSubdivisionDirections (second :: rest)) := by
  have sourceTailOrthogonal : OrthogonalPolyline (second :: rest) :=
    (List.isChain_cons_cons.mp sourceOrthogonal).2
  have doubledTailOrthogonal :
      OrthogonalPolyline (scalePolyline 2 (second :: rest)) :=
    sourceTailOrthogonal.scalePolyline (by norm_num)
  rw [unitSubdivisionDirections_translatePolyline]
  change unitSubdivisionDirections
      (scalePolyline 72
        (AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (second :: rest)))) = _
  calc
    _ = repeatDirections 72
          (unitSubdivisionDirections
            (AxisDirection.unitSubdividePolyline
              (scalePolyline 2 (second :: rest)))) := by
        simpa using unitSubdivisionDirections_scalePolyline
          72 (by norm_num)
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (second :: rest)))
    _ = repeatDirections 72
          (unitSubdivisionDirections
            (scalePolyline 2 (second :: rest))) := by
        rw [unitSubdivisionDirections_unitSubdividePolyline
          (scalePolyline 2 (second :: rest)) doubledTailOrthogonal]
    _ = repeatDirections 72
          (repeatDirections 2
            (unitSubdivisionDirections (second :: rest))) := by
        congr 1
        simpa using unitSubdivisionDirections_scalePolyline
          2 (by norm_num) (second :: rest)
    _ = repeatDirections 144
          (unitSubdivisionDirections (second :: rest)) := by
        rw [repeatDirections_repeatDirections]

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
