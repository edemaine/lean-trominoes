import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic

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
  deriving DecidableEq, Repr

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

end SquareSymmetry

/-- A placed copy records which prototile is used, its orientation, and its
translation. -/
structure Placement (ι : Type*) where
  kind : ι
  symmetry : SquareSymmetry
  offset : Cell
  deriving Repr

namespace Placement

/-- The cells occupied by a placed copy from a family of prototiles. -/
def cells {ι : Type*} (prototiles : ι → Polyomino) (placement : Placement ι) :
    Finset Cell :=
  (prototiles placement.kind).image fun cell =>
    Cell.add placement.offset (placement.symmetry.act cell)

end Placement

/-- The two free trominoes: the straight I tromino and the bent L tromino. -/
inductive Tromino
  | I
  | L
  deriving DecidableEq, Repr

namespace Tromino

/-- A canonical representative of each tromino, before applying symmetries and
translations. -/
def cells : Tromino → Polyomino
  | .I => {(0, 0), (1, 0), (2, 0)}
  | .L => {(0, 0), (1, 0), (0, 1)}

end Tromino

end LeanTrominoes
