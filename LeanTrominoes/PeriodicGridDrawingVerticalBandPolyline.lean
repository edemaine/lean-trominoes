/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingVerticalBand

/-!
# Polyline operations inside an open vertical band

Pointwise membership in the open three-period vertical halo is preserved by
the three operations used during degree-two contraction: horizontal period
translation, reversal, and joining two polylines.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

namespace PeriodicGridDrawing

/-- Every listed point of one polyline lies in the drawing's open vertical
halo. -/
def PolylineInExpandedVerticalBand
    (drawing : PeriodicGridDrawing) (route : List Cell) : Prop :=
  ∀ point ∈ route, drawing.PositionInExpandedVerticalBand point

/-- Translating a band point by a horizontal lattice period keeps it in the
same vertical band. -/
theorem positionInExpandedVerticalBand_add_periodTranslation_of_horizontal
    {drawing : PeriodicGridDrawing} {position translate : Cell}
    (inside : drawing.PositionInExpandedVerticalBand position)
    (horizontal : translate.2 = 0) :
    drawing.PositionInExpandedVerticalBand
      (Cell.add (drawing.periodTranslation translate) position) := by
  apply positionInExpandedVerticalBand_add_of_vertical_eq_zero inside
  simp [PeriodicGridDrawing.periodTranslation, Cell.scale, horizontal]

/-- A horizontal lattice-period translation preserves pointwise polyline
band membership. -/
theorem PolylineInExpandedVerticalBand.translatePeriod
    {drawing : PeriodicGridDrawing} {route : List Cell} {translate : Cell}
    (inside : drawing.PolylineInExpandedVerticalBand route)
    (horizontal : translate.2 = 0) :
    drawing.PolylineInExpandedVerticalBand
      (translatePolyline (drawing.periodTranslation translate) route) := by
  intro point pointMember
  simp only [translatePolyline, List.mem_map] at pointMember
  rcases pointMember with ⟨source, sourceMember, rfl⟩
  exact
    positionInExpandedVerticalBand_add_periodTranslation_of_horizontal
      (inside source sourceMember) horizontal

/-- Reversing a polyline preserves its set of points and hence its band
membership. -/
theorem PolylineInExpandedVerticalBand.reverse
    {drawing : PeriodicGridDrawing} {route : List Cell}
    (inside : drawing.PolylineInExpandedVerticalBand route) :
    drawing.PolylineInExpandedVerticalBand route.reverse := by
  intro point pointMember
  exact inside point (List.mem_reverse.mp pointMember)

/-- Joining two band-contained polylines cannot introduce a new point. -/
theorem PolylineInExpandedVerticalBand.joinPolylines
    {drawing : PeriodicGridDrawing} {first second : List Cell}
    (firstInside : drawing.PolylineInExpandedVerticalBand first)
    (secondInside : drawing.PolylineInExpandedVerticalBand second) :
    drawing.PolylineInExpandedVerticalBand
      (PeriodicOrthocrossing.joinPolylines first second) := by
  intro point pointMember
  simp only [PeriodicOrthocrossing.joinPolylines,
    List.mem_append] at pointMember
  rcases pointMember with firstMember | secondTailMember
  · exact firstInside point firstMember
  · exact secondInside point (List.mem_of_mem_tail secondTailMember)

end PeriodicGridDrawing
end LeanTrominoes
