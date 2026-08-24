/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineRibbon

/-! # Static first directions of retained carrier lenses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- The first compass direction of a route in an east- or north-facing
equality lens. -/
def compiledCarrierLensRouteFirstDirection
    (horizontal : Bool) : Nat → Nat → AxisDirection
  | 0, 0 => if horizontal then .west else .south
  | 0, 1 => if horizontal then .south else .east
  | 1, 0 => if horizontal then .north else .west
  | 1, 1 => if horizontal then .east else .north
  | _, _ => .invalid

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
