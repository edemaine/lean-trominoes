/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATEqualityLensPlacement

/-!
# Equality-link lens drawings

This file turns the placed equality-lens template into a small interface for
one positioned `EqualityLink`.  A caller only has to certify the geometry
already carried by the link: distinct endpoints, a sufficiently long
axis-aligned segment between their assigned positions, and agreement of the
two clause positions with the canonical offsets three and six.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EqualityLink

/-- The geometric facts needed to draw one equality link by a narrow lens. -/
structure LensGeometry
    {Variable : Type*} [DecidableEq Variable]
    (position : Variable → Cell) (link : EqualityLink Variable) : Prop where
  different : link.first ≠ link.second
  axisAligned :
    (GridSegment.mk
      (position link.first) (position link.second)).IsAxisAligned
  spanLarge :
    8 ≤ AxisDirection.axisSpan
      (position link.first) (position link.second)
  positions :
    link.positions =
      ⟨(AxisDirection.between
          (position link.first) (position link.second)).placePoint
          (position link.first) (3, 0),
        (AxisDirection.between
          (position link.first) (position link.second)).placePoint
          (position link.first) (6, 0)⟩

/-- Instantiate the equality lens using the endpoint positions of one link. -/
def lensDrawing
    {Variable : Type*} [DecidableEq Variable]
    (position : Variable → Cell) (link : EqualityLink Variable) :
    EmbeddedCNFIncidenceDrawing Variable :=
  placedEqualityLensDrawing link.first link.second
    (position link.first)
    (AxisDirection.between
      (position link.first) (position link.second))
    (AxisDirection.axisSpan
      (position link.first) (position link.second))

/-- A certified link lens contains exactly the two clauses represented by
the positioned equality link. -/
theorem lensDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    {position : Variable → Cell} {link : EqualityLink Variable}
    (geometry : LensGeometry position link) :
    (lensDrawing position link).formula =
      equalityInstance link.first link.second link.positions := by
  rw [lensDrawing, placedEqualityLensDrawing_formula, ← geometry.positions]

/-- A certified link lens places its first endpoint at the assigned point. -/
theorem lensDrawing_firstPosition
    {Variable : Type*} [DecidableEq Variable]
    {position : Variable → Cell} {link : EqualityLink Variable}
    (geometry : LensGeometry position link) :
    (lensDrawing position link).variablePosition link.first =
      position link.first := by
  exact placedEqualityLensDrawing_firstPosition geometry.different
    (position link.first)
    (AxisDirection.between
      (position link.first) (position link.second))
    (AxisDirection.axisSpan
      (position link.first) (position link.second))

/-- A certified link lens places its second endpoint at the assigned point. -/
theorem lensDrawing_secondPosition
    {Variable : Type*} [DecidableEq Variable]
    {position : Variable → Cell} {link : EqualityLink Variable}
    (geometry : LensGeometry position link) :
    (lensDrawing position link).variablePosition link.second =
      position link.second := by
  rw [lensDrawing,
    placedEqualityLensDrawing_secondPosition geometry.different,
    AxisDirection.placePoint_between_axisSpan geometry.axisAligned]

/-- The four local carrier facts imply the complete finite incidence-drawing
certificate for the equality lens. -/
theorem lensDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    {position : Variable → Cell} {link : EqualityLink Variable}
    (geometry : LensGeometry position link) :
    (lensDrawing position link).IsValid := by
  exact placedEqualityLensDrawing_isValid geometry.different
    (position link.first)
    (AxisDirection.between
      (position link.first) (position link.second))
    (AxisDirection.axisSpan
      (position link.first) (position link.second))
    geometry.spanLarge

end EqualityLink
end PlanarThreeSAT
end LeanTrominoes
