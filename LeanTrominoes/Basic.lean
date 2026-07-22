import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Basic definitions

Integer-lattice cells, polyominoes, square-grid symmetries, placements, and the
two tromino prototiles.
-/

namespace LeanTrominoes

/-- A unit-square cell, identified by its integer coordinates. -/
abbrev Cell := Int × Int

namespace Cell

/-- Coordinatewise addition of lattice cells/vectors. -/
def add (first second : Cell) : Cell :=
  (first.1 + second.1, first.2 + second.2)

/-- Integer scaling of a lattice vector. -/
def scale (coefficient : Int) (vector : Cell) : Cell :=
  (coefficient * vector.1, coefficient * vector.2)

/-- Translation by a fixed cell is injective. -/
theorem add_left_injective (offset : Cell) : Function.Injective (add offset) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ equality
  simp only [add, Prod.mk.injEq] at equality ⊢
  exact ⟨Int.add_left_cancel equality.1, Int.add_left_cancel equality.2⟩

end Cell

/-- A polyomino is a finite set of integer-lattice cells. Connectivity is not
built into the type because later results also use disconnected prototiles. -/
abbrev Polyomino := Finset Cell

/-- The eight symmetries of the square grid. A placement adds an arbitrary
integer translation after applying one of these symmetries. -/
inductive SquareSymmetry
  | identity
  | rotate90
  | rotate180
  | rotate270
  | reflectX
  | reflectDiagonal
  | reflectY
  | reflectAntidiagonal
  deriving DecidableEq, Fintype, Repr

namespace SquareSymmetry

/-- Act on an integer-lattice cell by a square-grid symmetry fixing the origin. -/
def act : SquareSymmetry → Cell → Cell
  | .identity, (x, y) => (x, y)
  | .rotate90, (x, y) => (-y, x)
  | .rotate180, (x, y) => (-x, -y)
  | .rotate270, (x, y) => (y, -x)
  | .reflectX, (x, y) => (x, -y)
  | .reflectDiagonal, (x, y) => (y, x)
  | .reflectY, (x, y) => (-x, y)
  | .reflectAntidiagonal, (x, y) => (-y, -x)

/-- The inverse square-grid symmetry. -/
def inverse : SquareSymmetry → SquareSymmetry
  | .identity => .identity
  | .rotate90 => .rotate270
  | .rotate180 => .rotate180
  | .rotate270 => .rotate90
  | .reflectX => .reflectX
  | .reflectDiagonal => .reflectDiagonal
  | .reflectY => .reflectY
  | .reflectAntidiagonal => .reflectAntidiagonal

@[simp]
theorem inverse_act_act (symmetry : SquareSymmetry) (cell : Cell) :
    symmetry.inverse.act (symmetry.act cell) = cell := by
  cases symmetry <;> rcases cell with ⟨x, y⟩ <;> simp [inverse, act]

@[simp]
theorem act_inverse_act (symmetry : SquareSymmetry) (cell : Cell) :
    symmetry.act (symmetry.inverse.act cell) = cell := by
  cases symmetry <;> rcases cell with ⟨x, y⟩ <;> simp [inverse, act]

/-- Every square-grid symmetry acts injectively on cells. -/
theorem act_injective (symmetry : SquareSymmetry) :
    Function.Injective symmetry.act :=
  Function.LeftInverse.injective fun cell => inverse_act_act symmetry cell

/-- A square-grid symmetry as an equivalence of lattice cells. -/
def cellEquiv (symmetry : SquareSymmetry) : Cell ≃ Cell where
  toFun := symmetry.act
  invFun := symmetry.inverse.act
  left_inv := inverse_act_act symmetry
  right_inv := act_inverse_act symmetry

end SquareSymmetry

/-- A placed copy records which prototile is used, its orientation, and its
translation. -/
structure Placement (ι : Type*) where
  kind : ι
  symmetry : SquareSymmetry
  offset : Cell
  deriving DecidableEq, Repr

namespace Placement

@[ext]
theorem ext {kind : Type*} {first second : Placement kind}
    (kind_eq : first.kind = second.kind)
    (symmetry_eq : first.symmetry = second.symmetry)
    (offset_eq : first.offset = second.offset) : first = second := by
  cases first
  cases second
  simp_all

/-- The map from a prototile cell to its position in a placement is injective. -/
theorem cellMap_injective {kind : Type*} (placement : Placement kind) :
    Function.Injective fun cell =>
      Cell.add placement.offset (placement.symmetry.act cell) := by
  intro first second equality
  apply placement.symmetry.act_injective
  exact Cell.add_left_injective placement.offset equality

/-- The cells occupied by a placed copy from a family of prototiles. -/
def cells {ι : Type*} (prototiles : ι → Polyomino) (placement : Placement ι) :
    Finset Cell :=
  (prototiles placement.kind).image fun cell =>
    Cell.add placement.offset (placement.symmetry.act cell)

/-- Characterization of membership in the occupied cells of a placement. -/
theorem mem_cells_iff {kind : Type*} (prototiles : kind → Polyomino)
    (placement : Placement kind) (cell : Cell) :
    cell ∈ placement.cells prototiles ↔
      ∃ source ∈ prototiles placement.kind,
        Cell.add placement.offset (placement.symmetry.act source) = cell := by
  simp [cells]

/-- Rigid motions preserve the number of cells in a prototile. -/
theorem card_cells {kind : Type*} (prototiles : kind → Polyomino)
    (placement : Placement kind) :
    (placement.cells prototiles).card = (prototiles placement.kind).card := by
  exact Finset.card_image_of_injective _ placement.cellMap_injective

end Placement

/-- The two free trominoes: the straight I tromino and the bent L tromino. -/
inductive Tromino
  | I
  | L
  deriving DecidableEq, Fintype, Repr

namespace Tromino

/-- A canonical representative of each tromino, before applying symmetries and
translations. -/
def cells : Tromino → Polyomino
  | .I => {(0, 0), (1, 0), (2, 0)}
  | .L => {(0, 0), (1, 0), (0, 1)}

@[simp]
theorem card_cells (tromino : Tromino) : tromino.cells.card = 3 := by
  cases tromino <;> decide

@[simp]
theorem card_placement_cells (tromino : Tromino) (placement : Placement Unit) :
    (placement.cells fun _ => tromino.cells).card = 3 := by
  rw [Placement.card_cells, card_cells]

/-- Because the canonical representatives contain the origin, every placed
tromino contains its offset cell. -/
theorem offset_mem_placement_cells (tromino : Tromino) (placement : Placement Unit) :
    placement.offset ∈ placement.cells fun _ => tromino.cells := by
  rw [Placement.mem_cells_iff]
  refine ⟨(0, 0), ?_, ?_⟩
  · cases tromino <;> simp [cells]
  · cases placement.symmetry <;> simp [SquareSymmetry.act, Cell.add]

end Tromino

end LeanTrominoes
