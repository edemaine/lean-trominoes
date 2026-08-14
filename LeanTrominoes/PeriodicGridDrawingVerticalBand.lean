/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingPointBounds

/-!
# Open vertical bands in periodic grid drawings

For a horizontally periodic strip we retain only the vertical part of the
usual open one-period halo.  A point in `(-P, 2P)` can be reflected and
shifted into the strict interior of a height-`3P` raster, leaving its two
boundary rows blank.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

/-- A point lies in the open vertical halo spanning three fundamental
periods. -/
def PositionInExpandedVerticalBand
    (drawing : PeriodicGridDrawing) (position : Cell) : Prop :=
  -(drawing.gridSize : Int) < position.2 ∧
    position.2 < 2 * drawing.gridSize

/-- Every listed point of every stored route lies in the open vertical
halo. -/
def RoutePointsInExpandedVerticalBand
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ route ∈ drawing.edgeRoutes,
    ∀ point ∈ route,
      drawing.PositionInExpandedVerticalBand point

/-- Full open-halo membership implies its vertical projection. -/
theorem positionInExpandedVerticalBand_of_expandedSquare
    {drawing : PeriodicGridDrawing} {position : Cell}
    (inside : drawing.PositionInExpandedSquare position) :
    drawing.PositionInExpandedVerticalBand position := by
  exact inside.2.2

/-- Fundamental-square membership also lies in the open vertical halo. -/
theorem positionInExpandedVerticalBand_of_fundamentalSquare
    {drawing : PeriodicGridDrawing} {position : Cell}
    (inside : drawing.PositionInFundamentalSquare position) :
    drawing.PositionInExpandedVerticalBand position :=
  positionInExpandedVerticalBand_of_expandedSquare
    (positionInExpandedSquare_of_fundamental inside)

/-- A point with the same vertical coordinate as a band point remains in
the band. -/
theorem positionInExpandedVerticalBand_of_vertical_eq
    {drawing : PeriodicGridDrawing} {first second : Cell}
    (inside : drawing.PositionInExpandedVerticalBand first)
    (vertical : second.2 = first.2) :
    drawing.PositionInExpandedVerticalBand second := by
  simpa only [PositionInExpandedVerticalBand, vertical] using inside

/-- Translating horizontally preserves the vertical band. -/
theorem positionInExpandedVerticalBand_add_of_vertical_eq_zero
    {drawing : PeriodicGridDrawing} {position translate : Cell}
    (inside : drawing.PositionInExpandedVerticalBand position)
    (horizontal : translate.2 = 0) :
    drawing.PositionInExpandedVerticalBand
      (Cell.add translate position) := by
  apply positionInExpandedVerticalBand_of_vertical_eq inside
  simp [Cell.add, horizontal]

/-- Full pointwise open-halo bounds imply the vertical-only route bound. -/
theorem routePointsInExpandedVerticalBand_of_expandedSquare
    {drawing : PeriodicGridDrawing}
    (inside : drawing.RoutePointsInExpandedSquare) :
    drawing.RoutePointsInExpandedVerticalBand := by
  intro route routeMember point pointMember
  exact positionInExpandedVerticalBand_of_expandedSquare
    (inside route routeMember point pointMember)

/-- Reflection followed by a shift of `2P` places every band point strictly
between the two boundaries of a height-`3P` raster. -/
theorem shiftedReflectedVertical_in_threePeriods
    {drawing : PeriodicGridDrawing} {position : Cell}
    (inside : drawing.PositionInExpandedVerticalBand position) :
    0 < 2 * (drawing.gridSize : Int) - position.2 ∧
      2 * (drawing.gridSize : Int) - position.2 <
        3 * drawing.gridSize := by
  simp only [PositionInExpandedVerticalBand] at inside
  omega

end PeriodicGridDrawing
end LeanTrominoes
