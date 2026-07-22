import LeanTrominoes.Tiling
import Mathlib.Computability.Primrec.List

/-!
# Finite presentations of periodic regions

The two-dimensional presentation is a finite motif repeated by the integer
span of two period vectors. The 1.5-dimensional presentation is a finite motif
in a strip fundamental domain, repeated in the unbounded direction.
-/

namespace LeanTrominoes

/-- Raw finite input describing a two-dimensional periodic subset. Malformed
inputs, whose period vectors are dependent, are rejected by the decision
problem rather than excluded from the encodable input type. -/
structure PeriodicRegionSpec where
  motif : List Cell
  period₁ : Cell
  period₂ : Cell
  deriving DecidableEq, Repr

namespace PeriodicRegionSpec

/-- Product representation used to obtain the standard computability encoding. -/
def equivData : PeriodicRegionSpec ≃ List Cell × Cell × Cell where
  toFun input := (input.motif, input.period₁, input.period₂)
  invFun data :=
    { motif := data.1
      period₁ := data.2.1
      period₂ := data.2.2 }
  left_inv input := by cases input; rfl
  right_inv data := by rcases data with ⟨motif, period₁, period₂⟩; rfl

instance : Primcodable PeriodicRegionSpec :=
  Primcodable.ofEquiv (List Cell × Cell × Cell) equivData

/-- Determinant of the two period vectors. -/
def determinant (input : PeriodicRegionSpec) : Int :=
  input.period₁.1 * input.period₂.2 - input.period₁.2 * input.period₂.1

/-- The input really describes a 2D-periodic region precisely when its two
period vectors are linearly independent. -/
def IsFullRank (input : PeriodicRegionSpec) : Prop :=
  input.determinant ≠ 0

/-- The infinite subset represented by the finite motif and its two periods. -/
def carrier (input : PeriodicRegionSpec) : Set Cell :=
  { cell | ∃ base ∈ input.motif, ∃ i j : Int,
      cell = Cell.add (Cell.add base (Cell.scale i input.period₁))
        (Cell.scale j input.period₂) }

end PeriodicRegionSpec

/-- Raw finite input for a 1.5-dimensional periodic subset. The ambient strip
is `ℤ × {0, ..., width - 1}`, and `period` is measured along its unbounded
coordinate. -/
structure PeriodicStripSpec where
  width : Nat
  period : Nat
  motif : List Cell
  deriving DecidableEq, Repr

namespace PeriodicStripSpec

/-- Product representation used to obtain the standard computability encoding. -/
def equivData : PeriodicStripSpec ≃ Nat × Nat × List Cell where
  toFun input := (input.width, input.period, input.motif)
  invFun data :=
    { width := data.1
      period := data.2.1
      motif := data.2.2 }
  left_inv input := by cases input; rfl
  right_inv data := by rcases data with ⟨width, period, motif⟩; rfl

instance : Primcodable PeriodicStripSpec :=
  Primcodable.ofEquiv (Nat × Nat × List Cell) equivData

/-- Membership in the chosen rectangular fundamental domain of a strip input. -/
def InFundamentalDomain (input : PeriodicStripSpec) (cell : Cell) : Prop :=
  0 ≤ cell.1 ∧ cell.1 < (input.period : Int) ∧
    0 ≤ cell.2 ∧ cell.2 < (input.width : Int)

/-- A well-formed strip input has positive width and period, and stores its
motif inside the selected fundamental domain. -/
def IsWellFormed (input : PeriodicStripSpec) : Prop :=
  0 < input.width ∧ 0 < input.period ∧
    ∀ cell ∈ input.motif, input.InFundamentalDomain cell

/-- The infinite periodic subset of the strip represented by `input`. -/
def carrier (input : PeriodicStripSpec) : Set Cell :=
  { cell | 0 ≤ cell.2 ∧ cell.2 < (input.width : Int) ∧
      ∃ base ∈ input.motif, ∃ i : Int,
        cell = Cell.add base (Cell.scale i (((input.period : Int), 0) : Cell)) }

end PeriodicStripSpec

/-- The 2D periodic-subset tiling decision predicate for a fixed tromino.
Dependent-period inputs are defined to be no-instances. -/
def PeriodicTrominoTiling (tromino : Tromino) (input : PeriodicRegionSpec) : Prop :=
  input.IsFullRank ∧ tromino.Tileable input.carrier

/-- The 1.5D periodic-subset tiling decision predicate for a fixed tromino.
Malformed strip presentations are defined to be no-instances. -/
def PeriodicStripTrominoTiling (tromino : Tromino) (input : PeriodicStripSpec) : Prop :=
  input.IsWellFormed ∧ tromino.Tileable input.carrier

end LeanTrominoes
