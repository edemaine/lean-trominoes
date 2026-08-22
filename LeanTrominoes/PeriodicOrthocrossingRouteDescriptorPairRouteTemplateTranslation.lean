/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCoreTemplateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteTemplates

/-! # Translation semantics of local affine route templates -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Each core shape translates an arbitrary affine point by exactly the local
period offset named by its semantic branch condition. -/
theorem CoreShape.evalPair_translatePoint
    (shape : CoreShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) (affinePoint : Point)
    (shapeMatches : shape.Matches (descriptorAt pair side)) :
    (shape.translatePoint side affinePoint).evalPair pair =
      Cell.add (affinePoint.evalPair pair)
        (Cell.scale ((descriptorAt pair side).gridSize : Int)
          (descriptorAt pair side).offset) := by
  have sizeEq :
      Expression.eval (pairFieldValue pair) (gridSize side) =
        ((descriptorAt pair side).gridSize : Int) :=
    evalPair_gridSize pair side
  cases shape with
  | zero =>
      simp [CoreShape.translatePoint,
        show (descriptorAt pair side).offset = (0, 0) from shapeMatches,
        Cell.add, Cell.scale]
  | positiveHorizontalDirect =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.translatePoint, offset, sizeEq,
        Point.evalPair, Point.eval, point, Cell.add, Cell.scale]
  | positiveHorizontalBent =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.translatePoint, offset, sizeEq,
        Point.evalPair, Point.eval, point, Cell.add, Cell.scale]
  | negativeHorizontalDirect =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.translatePoint, offset, sizeEq,
        Point.evalPair, Point.eval, point, Cell.add, Cell.scale,
        sub_eq_add_neg]
  | negativeHorizontalBent =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.translatePoint, offset, sizeEq,
        Point.evalPair, Point.eval, point, Cell.add, Cell.scale,
        sub_eq_add_neg]
  | positiveVertical =>
      simp [CoreShape.translatePoint,
        show (descriptorAt pair side).offset = (0, 1) from shapeMatches,
        sizeEq, Point.evalPair, Point.eval, point,
        Cell.add, Cell.scale]
  | negativeVertical =>
      simp [CoreShape.translatePoint,
        show (descriptorAt pair side).offset = (0, -1) from shapeMatches,
        sizeEq, Point.evalPair, Point.eval, point,
        Cell.add, Cell.scale, sub_eq_add_neg]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
