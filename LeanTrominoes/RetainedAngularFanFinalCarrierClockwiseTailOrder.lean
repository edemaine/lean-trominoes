/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceTailData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDirections

/-! # Clockwise order of retained-carrier route tails -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

private def carrierAnnotatedTail
    (horizontal : Bool)
    (localClauseIndex literalIndex : Nat)
    (tail : List AxisDirection) : AnnotatedTail where
  profile := default
  firstDirection := carrierLensRouteFirstDirection
    horizontal localClauseIndex literalIndex
  sourceTailDirections := tail

/-- Clockwise sorting reverses the two forward carrier routes for either
physical carrier axis. -/
theorem carrierForwardTailDirections_clockwise
    (horizontal : Bool)
    (first second : List AxisDirection) :
    ([carrierAnnotatedTail horizontal 0 0 first,
      carrierAnnotatedTail horizontal 0 1 second].insertionSort
        directionLE).map AnnotatedTail.sourceTailDirections =
      [second, first] := by
  cases horizontal <;>
    simp [carrierAnnotatedTail, directionLE,
      AnnotatedTail.key,
      PeriodicCNF.FormulaShapeDirectionOrdering.directionLE,
      carrierLensRouteFirstDirection, AxisDirection.clockwiseRank]

/-- Clockwise sorting reverses the backward carrier routes exactly for a
horizontal physical carrier. -/
theorem carrierBackwardTailDirections_clockwise
    (horizontal : Bool)
    (first second : List AxisDirection) :
    ([carrierAnnotatedTail horizontal 1 0 first,
      carrierAnnotatedTail horizontal 1 1 second].insertionSort
        directionLE).map AnnotatedTail.sourceTailDirections =
      if horizontal then [second, first] else [first, second] := by
  cases horizontal <;>
    simp [carrierAnnotatedTail, directionLE,
      AnnotatedTail.key,
      PeriodicCNF.FormulaShapeDirectionOrdering.directionLE,
      carrierLensRouteFirstDirection, AxisDirection.clockwiseRank]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
