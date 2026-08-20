/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteData
import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.OrthogonalPolylineUnitSubdivision

/-! # Executable horizontal occurrence-route preprocessing -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Subdivide every segment of the selected horizontal occurrence route into
ordered unit lattice steps. -/
def horizontalOccurrenceUnitSourceRouteComputed
    (input : HorizontalOccurrenceRouteInput) : List Cell :=
  AxisDirection.unitSubdividePolyline
    (horizontalOccurrenceSourceRouteComputed input)

/-- Direction in which the executable unit route leaves its variable. -/
def horizontalOccurrenceSourceVariableDirectionComputed
    (input : HorizontalOccurrenceRouteInput) : AxisDirection :=
  AxisDirection.polylineFirstDirection
    (horizontalOccurrenceUnitSourceRouteComputed input)

/-- Direction in which the executable unit route enters its clause. -/
def horizontalOccurrenceSourceClauseDirectionComputed
    (input : HorizontalOccurrenceRouteInput) : AxisDirection :=
  AxisDirection.polylineLastDirection
    (horizontalOccurrenceUnitSourceRouteComputed input)

end PeriodicCNFStripReduction
end LeanTrominoes
