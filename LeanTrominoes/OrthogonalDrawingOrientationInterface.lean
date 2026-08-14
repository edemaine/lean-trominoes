/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalDrawing

/-!
# Projection interface for valid periodic drawing orientations

These abstract accessors prevent downstream proofs from repeatedly unfolding
a large concrete drawing while specializing the two fields of `IsOrientation`.
-/

namespace LeanTrominoes

open Gadget

namespace Gadget.PeriodicOrthogonalDrawing.IsOrientation

/-- The local-orientation obligation at one location, named so concrete large
drawings need not be unfolded while specializing an orientation proof. -/
structure LocalConstraintAt
    (drawing : PeriodicOrthogonalDrawing)
    (orientation : drawing.Orientation) (location : Cell) : Prop where
  property : satisfiesOrientation
    (drawing.getAt location) (orientation location)

/-- The exposed-neighbor obligation at one location and side. -/
structure NeighborCompatibilityAt
    (drawing : PeriodicOrthogonalDrawing)
    (orientation : drawing.Orientation) (location : Cell) (side : Side) : Prop where
  property : ((drawing.getAt location).portColor side).isSome →
    orientation location side =
      !(orientation (latticeNeighbor location side) side.opposite)

/-- A valid orientation satisfies the local constraint at any location. -/
theorem localConstraint
    {drawing : PeriodicOrthogonalDrawing}
    {orientation : drawing.Orientation}
    (valid : drawing.IsOrientation orientation) (location : Cell) :
    LocalConstraintAt drawing orientation location :=
  ⟨valid.1 location⟩

/-- A valid orientation gives complementary values across any exposed port. -/
theorem neighborCompatibility
    {drawing : PeriodicOrthogonalDrawing}
    {orientation : drawing.Orientation}
    (valid : drawing.IsOrientation orientation)
    (location : Cell) (side : Side) :
    NeighborCompatibilityAt drawing orientation location side :=
  ⟨valid.2 location side⟩

end Gadget.PeriodicOrthogonalDrawing.IsOrientation

end LeanTrominoes
