import LeanTrominoes.GadgetPorts
import Mathlib.Data.ZMod.Basic

/-!
# Normalized periodic orthogonal graph drawings

The hardness proof first normalizes a planar trichromatic graph drawing so
that every grid square is blank, a colored wire segment or bend, a
monochromatic 1-in-3 vertex, or a trichromatic 0-or-3-in-3 vertex.  This file
defines that finite toroidal source problem independently of the tromino
implementation of each local cell.
-/

namespace LeanTrominoes
namespace Gadget

/-- The side opposite a cardinal side. -/
def Side.opposite : Side → Side
  | .north => .south
  | .east => .west
  | .south => .north
  | .west => .east

@[simp]
theorem Side.opposite_opposite (side : Side) :
    side.opposite.opposite = side := by
  cases side <;> rfl

/-- The edge color, if any, meeting one side of a normalized drawing cell. -/
def OrthogonalCellType.portColor : OrthogonalCellType → Side → Option WireColor
  | .blank, _ => none
  | .wire .horizontal color, .east
  | .wire .horizontal color, .west => some color
  | .wire .vertical color, .north
  | .wire .vertical color, .south => some color
  | .wire _ _, _ => none
  | .bend .northeast color, .north
  | .bend .northeast color, .east => some color
  | .bend .northwest color, .north
  | .bend .northwest color, .west => some color
  | .bend .southeast color, .south
  | .bend .southeast color, .east => some color
  | .bend .southwest color, .south
  | .bend .southwest color, .west => some color
  | .bend _ _, _ => none
  | .monochromaticVertex color, .west
  | .monochromaticVertex color, .north
  | .monochromaticVertex color, .east => some color
  | .monochromaticVertex _, .south => none
  | .trichromaticVertex .blueRedGreen, .west => some .blue
  | .trichromaticVertex .blueRedGreen, .north => some .red
  | .trichromaticVertex .blueRedGreen, .east => some .green
  | .trichromaticVertex .greenRedBlue, .west => some .green
  | .trichromaticVertex .greenRedBlue, .north => some .red
  | .trichromaticVertex .greenRedBlue, .east => some .blue
  | .trichromaticVertex _, .south => none

/-- A finite fundamental domain for a normalized periodic orthogonal drawing.
The stored dimensions are predecessors, making both actual periods positive
by construction. -/
structure PeriodicOrthogonalDrawing where
  horizontalPeriodPred : Nat
  verticalPeriodPred : Nat
  cellType : Fin (horizontalPeriodPred + 1) →
    Fin (verticalPeriodPred + 1) → OrthogonalCellType

namespace PeriodicOrthogonalDrawing

/-- A grid position in the drawing's finite toroidal fundamental domain. -/
abbrev Position (drawing : PeriodicOrthogonalDrawing) :=
  Fin (drawing.horizontalPeriodPred + 1) ×
    Fin (drawing.verticalPeriodPred + 1)

/-- The local cell type at a torus position. -/
def get (drawing : PeriodicOrthogonalDrawing) (position : drawing.Position) :
    OrthogonalCellType :=
  drawing.cellType position.1 position.2

/-- Move one unit across the toroidal drawing grid. -/
def neighbor (drawing : PeriodicOrthogonalDrawing)
    (position : drawing.Position) : Side → drawing.Position
  | .north => (position.1, position.2 - 1)
  | .east => (position.1 + 1, position.2)
  | .south => (position.1, position.2 + 1)
  | .west => (position.1 - 1, position.2)

@[simp]
theorem neighbor_opposite (drawing : PeriodicOrthogonalDrawing)
    (position : drawing.Position) (side : Side) :
    drawing.neighbor (drawing.neighbor position side) side.opposite = position := by
  cases side <;> ext <;> simp [neighbor, Side.opposite]

/-- Every colored half-edge meets a half-edge of the same color in the
neighboring cell; unused sides likewise meet unused sides. -/
def IsWellFormed (drawing : PeriodicOrthogonalDrawing) : Prop :=
  ∀ position side,
    (drawing.get position).portColor side =
      (drawing.get (drawing.neighbor position side)).portColor side.opposite

instance (drawing : PeriodicOrthogonalDrawing) :
    Decidable drawing.IsWellFormed := by
  unfold IsWellFormed
  infer_instance

/-- A half-edge value is `true` exactly when that half-edge points into its
current local cell. -/
abbrev Orientation (drawing : PeriodicOrthogonalDrawing) :=
  drawing.Position → Side → Bool

/-- The local orientation constraint of one normalized drawing cell. -/
def satisfiesOrientation (cellType : OrthogonalCellType)
    (inward : Side → Bool) : Prop :=
  match cellType with
  | .blank => True
  | .wire .horizontal _ => inward .west ≠ inward .east
  | .wire .vertical _ => inward .north ≠ inward .south
  | .bend .northeast _ => inward .north ≠ inward .east
  | .bend .northwest _ => inward .north ≠ inward .west
  | .bend .southeast _ => inward .south ≠ inward .east
  | .bend .southwest _ => inward .south ≠ inward .west
  | .monochromaticVertex _ =>
      [inward .west, inward .north, inward .east].count true = 1
  | .trichromaticVertex _ =>
      inward .west = inward .north ∧ inward .north = inward .east

instance (cellType : OrthogonalCellType) (inward : Side → Bool) :
    Decidable (satisfiesOrientation cellType inward) := by
  unfold satisfiesOrientation
  split <;> infer_instance

/-- A global orientation satisfies every local vertex/subdivision constraint
and assigns opposite inward values to the two ends of every colored edge. -/
def IsOrientation (drawing : PeriodicOrthogonalDrawing)
  (orientation : drawing.Orientation) : Prop :=
  (∀ position,
    satisfiesOrientation (drawing.get position) (orientation position)) ∧
  ∀ position side,
    ((drawing.get position).portColor side).isSome →
      orientation position side =
        !(orientation (drawing.neighbor position side) side.opposite)

instance (drawing : PeriodicOrthogonalDrawing)
    (orientation : drawing.Orientation) :
    Decidable (drawing.IsOrientation orientation) := by
  unfold IsOrientation
  infer_instance

/-- The normalized periodic drawing has a valid trichromatic graph
orientation. -/
def HasOrientation (drawing : PeriodicOrthogonalDrawing) : Prop :=
  drawing.IsWellFormed ∧ ∃ orientation, drawing.IsOrientation orientation

instance (drawing : PeriodicOrthogonalDrawing) :
    Decidable drawing.HasOrientation := by
  unfold HasOrientation
  infer_instance

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
