/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingMapPoints
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.OrthogonalPolylineRibbon
import Mathlib.Tactic

/-!
# Signed-axis placement of finite incidence drawings

The canonical equality lens points east from the origin.  Actual carrier
links can point along any of the four directed grid axes.  This file defines
the corresponding integral quarter turns, proves that they instantiate
`GridDrawingMap`, and combines rotation with translation into one certified
placement operation.
-/

namespace LeanTrominoes

namespace AxisDirection

/-- Rotate an east-facing point so its positive first coordinate points in
the selected grid direction.  The total invalid case is the identity. -/
def orientPoint : AxisDirection → Cell → Cell
  | .east, point => point
  | .north, point => (-point.2, point.1)
  | .west, point => (-point.1, -point.2)
  | .south, point => (point.2, -point.1)
  | .invalid, point => point

/-- Orient a canonical point and translate its origin. -/
def placePoint
    (origin : Cell) (direction : AxisDirection) (point : Cell) :
    Cell :=
  Cell.add origin (direction.orientPoint point)

/-- Lattice length of an axis-aligned segment, written as an integer so it
can parameterize finite templates directly. -/
def axisSpan (first second : Cell) : Int :=
  |second.1 - first.1| + |second.2 - first.2|

/-- Every signed-axis orientation is injective. -/
theorem orientPoint_injective (direction : AxisDirection) :
    Function.Injective direction.orientPoint := by
  intro first second equal
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  cases direction <;>
    simp [orientPoint] at equal ⊢ <;>
    omega

/-- Orienting a canonical segment by the direction between two genuine
axis-aligned endpoints recovers the second endpoint exactly. -/
theorem placePoint_between_axisSpan
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (between first second).placePoint first
        (axisSpan first second, 0) =
      second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
    GridSegment.IsVertical] at aligned
  simp only [placePoint, axisSpan, between, orientPoint, Cell.add]
  split_ifs <;>
    simp_all [abs_of_nonneg, abs_of_nonpos]
  all_goals try omega
  · have absolute :
        |secondX - firstX| = secondX - firstX :=
      abs_of_pos (by omega)
    omega
  · have absolute :
        |secondY - firstY| = secondY - firstY :=
      abs_of_pos (by omega)
    omega

/-- Signed-axis orientation preserves nondegenerate axis alignment. -/
theorem isAxisAligned_orientPoint
    (direction : AxisDirection) (segment : GridSegment)
    (aligned : segment.IsAxisAligned) :
    (segment.mapPoints direction.orientPoint).IsAxisAligned := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  cases direction <;>
    simp [orientPoint, GridSegment.mapPoints,
      GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical] at aligned ⊢ <;>
    aesop

/-- Signed-axis orientation preserves and reflects point membership in a
segment's relative interior. -/
theorem interiorContains_orientPoint_iff
    (direction : AxisDirection)
    (segment : GridSegment) (point : Cell) :
    (segment.mapPoints direction.orientPoint).InteriorContains
        (direction.orientPoint point) ↔
      segment.InteriorContains point := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  cases direction <;>
    simp [orientPoint, GridSegment.mapPoints,
      GridSegment.InteriorContains, GridSegment.StrictlyBetween,
      GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
    aesop

/-- Signed-axis orientation preserves and reflects continuous relative-
interior intersection of two segments. -/
theorem interiorsMeet_orientPoint_iff
    (direction : AxisDirection)
    (first second : GridSegment) :
    GridSegment.InteriorsMeet
        (first.mapPoints direction.orientPoint)
        (second.mapPoints direction.orientPoint) ↔
      GridSegment.InteriorsMeet first second := by
  rcases first with
    ⟨⟨firstStartX, firstStartY⟩,
      ⟨firstFinishX, firstFinishY⟩⟩
  rcases second with
    ⟨⟨secondStartX, secondStartY⟩,
      ⟨secondFinishX, secondFinishY⟩⟩
  cases direction <;>
    simp [orientPoint, GridSegment.mapPoints,
      GridSegment.InteriorsMeet,
      GridSegment.OpenIntervalsOverlap,
      GridSegment.StrictlyBetween,
      GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
    aesop

end AxisDirection

namespace PlanarThreeSAT

/-- Every signed-axis quarter turn is a certified drawing map. -/
def axisDirectionGridDrawingMap (direction : AxisDirection) :
    GridDrawingMap direction.orientPoint where
  injective := direction.orientPoint_injective
  isAxisAligned := fun {_} aligned =>
    direction.isAxisAligned_orientPoint _ aligned
  interiorContains_iff := fun {_ _} =>
    direction.interiorContains_orientPoint_iff _ _
  interiorsMeet_iff := fun {_ _} =>
    direction.interiorsMeet_orientPoint_iff _ _

/-- Rotate a finite incidence drawing from east into a selected directed
axis. -/
def EmbeddedCNFIncidenceDrawing.orient
    {Variable : Type*}
    (direction : AxisDirection)
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    EmbeddedCNFIncidenceDrawing Variable :=
  drawing.mapPoints direction.orientPoint

/-- Rotate an incidence drawing and then translate its canonical origin. -/
def EmbeddedCNFIncidenceDrawing.placeOnAxis
    {Variable : Type*}
    (origin : Cell) (direction : AxisDirection)
  (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    EmbeddedCNFIncidenceDrawing Variable :=
  (drawing.orient direction).translate origin

/-- Signed-axis rotation preserves a complete drawing certificate. -/
theorem EmbeddedCNFIncidenceDrawing.isValid_orient
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (valid : drawing.IsValid)
    (direction : AxisDirection) :
    (drawing.orient direction).IsValid :=
  EmbeddedCNFIncidenceDrawing.isValid_mapPoints
    (axisDirectionGridDrawingMap direction) valid

/-- Signed-axis rotation followed by arbitrary translation preserves a
complete drawing certificate. -/
theorem EmbeddedCNFIncidenceDrawing.isValid_placeOnAxis
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (valid : drawing.IsValid)
    (origin : Cell) (direction : AxisDirection) :
    (drawing.placeOnAxis origin direction).IsValid :=
  EmbeddedCNFIncidenceDrawing.isValid_translate
    (EmbeddedCNFIncidenceDrawing.isValid_orient
      valid direction) origin

end PlanarThreeSAT
end LeanTrominoes
