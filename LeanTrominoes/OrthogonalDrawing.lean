/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetPorts
import Mathlib.Computability.Primrec.List
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

open Encodable

noncomputable instance : Primcodable WireColor :=
  Primcodable.ofEquiv (Fin (Fintype.card WireColor))
    (Fintype.equivFin WireColor)

noncomputable instance : Primcodable WireAxis :=
  Primcodable.ofEquiv (Fin (Fintype.card WireAxis))
    (Fintype.equivFin WireAxis)

noncomputable instance : Primcodable WireBend :=
  Primcodable.ofEquiv (Fin (Fintype.card WireBend))
    (Fintype.equivFin WireBend)

noncomputable instance : Primcodable TrichromaticOrder :=
  Primcodable.ofEquiv (Fin (Fintype.card TrichromaticOrder))
    (Fintype.equivFin TrichromaticOrder)

noncomputable instance : Primcodable OrthogonalCellType :=
  Primcodable.ofEquiv (Fin (Fintype.card OrthogonalCellType))
    (Fintype.equivFin OrthogonalCellType)

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

/-- Degree-three drawing cells.  The orthogonal normalization used by the
gadget reduction separates these cells by degree-two routing cells. -/
def OrthogonalCellType.isVertex : OrthogonalCellType → Bool
  | .monochromaticVertex _ | .trichromaticVertex _ => true
  | _ => false

/-- A finite fundamental domain for a normalized periodic orthogonal drawing.
The stored dimensions are predecessors, making both actual periods positive
by construction. -/
structure PeriodicOrthogonalDrawing where
  horizontalPeriodPred : Nat
  verticalPeriodPred : Nat
  cellTypes : List OrthogonalCellType

namespace PeriodicOrthogonalDrawing

/-- Product representation used by the standard computability encoding. -/
def equivData : PeriodicOrthogonalDrawing ≃
    Nat × Nat × List OrthogonalCellType where
  toFun drawing :=
    (drawing.horizontalPeriodPred, drawing.verticalPeriodPred,
      drawing.cellTypes)
  invFun data :=
    { horizontalPeriodPred := data.1
      verticalPeriodPred := data.2.1
      cellTypes := data.2.2 }
  left_inv drawing := by cases drawing; rfl
  right_inv data := by rcases data with ⟨horizontal, vertical, cells⟩; rfl

noncomputable instance : Primcodable PeriodicOrthogonalDrawing :=
  Primcodable.ofEquiv (Nat × Nat × List OrthogonalCellType) equivData

/-- A grid position in the drawing's finite toroidal fundamental domain. -/
abbrev Position (drawing : PeriodicOrthogonalDrawing) :=
  Fin (drawing.horizontalPeriodPred + 1) ×
    Fin (drawing.verticalPeriodPred + 1)

/-- The local cell type at a torus position. -/
def get (drawing : PeriodicOrthogonalDrawing) (position : drawing.Position) :
    OrthogonalCellType :=
  drawing.cellTypes.getD
    (position.2.val * (drawing.horizontalPeriodPred + 1) + position.1.val)
    .blank

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
  drawing.cellTypes.length =
      (drawing.horizontalPeriodPred + 1) * (drawing.verticalPeriodPred + 1) ∧
    ∀ position side,
      (drawing.get position).portColor side =
      (drawing.get (drawing.neighbor position side)).portColor side.opposite

instance (drawing : PeriodicOrthogonalDrawing) :
    Decidable drawing.IsWellFormed := by
  unfold IsWellFormed
  infer_instance

/-- The normalized drawing has at least one routing cell between every pair
of degree-three vertices. -/
def VerticesSeparated (drawing : PeriodicOrthogonalDrawing) : Prop :=
  ∀ position side,
    (drawing.get position).isVertex = true →
      (drawing.get (drawing.neighbor position side)).isVertex = false

instance (drawing : PeriodicOrthogonalDrawing) :
    Decidable drawing.VerticesSeparated := by
  unfold VerticesSeparated
  infer_instance

/-- The residue class of an integer coordinate in one positive drawing
period, represented as a finite index. -/
def residue (coordinate : Int) (periodPred : Nat) : Fin (periodPred + 1) :=
  ⟨(coordinate % (periodPred + 1)).toNat, by
    rw [Int.toNat_lt (Int.emod_nonneg coordinate (by omega))]
    exact Int.emod_lt_of_pos coordinate (by omega)⟩

/-- The finite residue index coerces back to the Euclidean remainder. -/
theorem residue_val_int (coordinate : Int) (periodPred : Nat) :
    ((residue coordinate periodPred).val : Int) =
      coordinate % (periodPred + 1) := by
  rw [residue, Int.toNat_of_nonneg]
  exact Int.emod_nonneg coordinate (by omega)

/-- Adding an integer multiple of the positive period does not change the
finite residue index. -/
@[simp]
theorem residue_add_period {periodPred : Nat}
    (position : Fin (periodPred + 1))
    (multiple : Int) :
    residue ((position.val : Int) + multiple * (periodPred + 1)) periodPred =
      position := by
  apply Fin.ext
  simp only [residue]
  have nonnegative : (0 : Int) ≤ (position.val : Int) := by positivity
  have below : (position.val : Int) < (periodPred + 1 : Nat) := by
    exact_mod_cast position.isLt
  have modulo :
      ((position.val : Int) + multiple * (periodPred + 1)) %
          (periodPred + 1) = position.val := by
    rw [Int.add_emod]
    simp
    exact Int.emod_eq_of_lt nonnegative below
  rw [modulo]
  simp

/-- Residue projection commutes with adding one in the finite cyclic index. -/
@[simp]
theorem residue_add_one (coordinate : Int) (periodPred : Nat) :
    residue (coordinate + 1) periodPred = residue coordinate periodPred + 1 := by
  let modulus : Int := periodPred + 1
  have modulusPos : 0 < modulus := by simp [modulus]
  have modulusToNat : modulus.toNat = periodPred + 1 := by simp [modulus]
  have remainderNonnegative : 0 ≤ coordinate % modulus :=
    Int.emod_nonneg coordinate (by omega)
  have remainderBelow : (coordinate % modulus).toNat < periodPred + 1 := by
    rw [Int.toNat_lt (Int.emod_nonneg coordinate (by omega))]
    exact Int.emod_lt_of_pos coordinate modulusPos
  have oneRemainder : (1 % modulus).toNat = 1 % (periodPred + 1) := by
    rw [Int.toNat_emod (by omega) (le_of_lt modulusPos)]
    simp [modulus]
  apply Fin.ext
  simp only [residue, Fin.add_def, Fin.val_mk]
  rw [Int.add_emod]
  change ((coordinate % modulus + 1 % modulus) % modulus).toNat = _
  rw [Int.toNat_emod]
  · rw [Int.toNat_add remainderNonnegative
        (Int.emod_nonneg 1 (by omega)), oneRemainder]
    rw [Nat.add_mod]
    rw [modulusToNat, Nat.mod_eq_of_lt remainderBelow]
    simp [modulus]
  · exact Int.add_nonneg remainderNonnegative
      (Int.emod_nonneg 1 (by omega))
  · omega

/-- Residue projection commutes with subtracting one in the finite cyclic
index. -/
@[simp]
theorem residue_sub_one (coordinate : Int) (periodPred : Nat) :
    residue (coordinate - 1) periodPred = residue coordinate periodPred - 1 := by
  have addOne := residue_add_one (coordinate - 1) periodPred
  simp only [sub_add_cancel] at addOne
  rw [addOne]
  simp

/-- Project an arbitrary cell of the infinite periodic lift to the stored
finite toroidal fundamental domain. -/
def positionAt (drawing : PeriodicOrthogonalDrawing) (location : Cell) :
    drawing.Position :=
  (residue location.1 drawing.horizontalPeriodPred,
    residue location.2 drawing.verticalPeriodPred)

/-- Explicit period translates of a fundamental-domain position project back
to that position. -/
@[simp]
theorem positionAt_add_periods (drawing : PeriodicOrthogonalDrawing)
    (position : drawing.Position) (horizontal vertical : Int) :
    drawing.positionAt
      ((position.1.val : Int) +
          horizontal * (drawing.horizontalPeriodPred + 1),
        (position.2.val : Int) +
          vertical * (drawing.verticalPeriodPred + 1)) = position := by
  apply Prod.ext
  · exact residue_add_period position.1 horizontal
  · exact residue_add_period position.2 vertical

/-- The normalized drawing-cell type at an arbitrary location in its infinite
periodic lift. -/
def getAt (drawing : PeriodicOrthogonalDrawing) (location : Cell) :
    OrthogonalCellType :=
  drawing.get (drawing.positionAt location)

/-- Move one unit in the infinite square grid. -/
def latticeNeighbor (location : Cell) : Side → Cell
  | .north => (location.1, location.2 - 1)
  | .east => (location.1 + 1, location.2)
  | .south => (location.1, location.2 + 1)
  | .west => (location.1 - 1, location.2)

/-- Moving in the infinite lift commutes with projection to the finite
toroidal fundamental domain. -/
@[simp]
theorem positionAt_latticeNeighbor (drawing : PeriodicOrthogonalDrawing)
    (location : Cell) (side : Side) :
    drawing.positionAt (latticeNeighbor location side) =
      drawing.neighbor (drawing.positionAt location) side := by
  cases side <;> apply Prod.ext <;>
    simp [positionAt, latticeNeighbor, neighbor]

/-- Finite well-formedness gives matching port colors at every adjacent pair
in the infinite periodic lift. -/
theorem portColor_latticeNeighbor_eq (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed) (location : Cell) (side : Side) :
    (drawing.getAt location).portColor side =
      (drawing.getAt (latticeNeighbor location side)).portColor side.opposite := by
  rw [getAt, getAt, positionAt_latticeNeighbor]
  exact wellFormed.2 (drawing.positionAt location) side

/-- Finite vertex separation lifts to every adjacent pair in the infinite
periodic drawing. -/
theorem verticesSeparatedAt (drawing : PeriodicOrthogonalDrawing)
    (separated : drawing.VerticesSeparated) (location : Cell) (side : Side)
    (isVertex : (drawing.getAt location).isVertex = true) :
    (drawing.getAt (latticeNeighbor location side)).isVertex = false := by
  change (drawing.get
    (drawing.positionAt (latticeNeighbor location side))).isVertex = false
  change (drawing.get (drawing.positionAt location)).isVertex = true at isVertex
  rw [positionAt_latticeNeighbor]
  exact separated (drawing.positionAt location) side isVertex

@[simp]
theorem latticeNeighbor_opposite (location : Cell) (side : Side) :
    latticeNeighbor (latticeNeighbor location side) side.opposite = location := by
  cases side <;> simp [latticeNeighbor, Side.opposite]

/-- A half-edge value on the infinite periodic lift is `true` exactly when
that half-edge points into its current drawing cell. Solutions are not assumed
to share the input periods. -/
abbrev Orientation (_drawing : PeriodicOrthogonalDrawing) :=
  Cell → Side → Bool

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
  (∀ location,
    satisfiesOrientation (drawing.getAt location) (orientation location)) ∧
  ∀ location side,
    ((drawing.getAt location).portColor side).isSome →
      orientation location side =
        !(orientation (latticeNeighbor location side) side.opposite)

/-- The normalized periodic drawing has a valid trichromatic graph
orientation. -/
def HasOrientation (drawing : PeriodicOrthogonalDrawing) : Prop :=
  drawing.IsWellFormed ∧ ∃ orientation, drawing.IsOrientation orientation

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
