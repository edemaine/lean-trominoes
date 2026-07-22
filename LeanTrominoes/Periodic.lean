import LeanTrominoes.Tiling
import Mathlib.Computability.Primrec.List

/-!
# Finite presentations of periodic regions

The two-dimensional presentation is a finite motif repeated by the integer
span of two period vectors. The 1.5-dimensional presentation is a finite motif
in a strip fundamental domain, repeated in the unbounded direction.
-/

namespace LeanTrominoes

/-- A finite presentation of a two-dimensional periodic subset. Presentations
whose period vectors are dependent are rejected by the decision problem rather
than excluded from the encodable type. -/
structure PeriodicRegion where
  motif : List Cell
  period₁ : Cell
  period₂ : Cell
  deriving DecidableEq, Repr

namespace PeriodicRegion

/-- Product representation used to obtain the standard computability encoding. -/
def equivData : PeriodicRegion ≃ List Cell × Cell × Cell where
  toFun periodicRegion :=
    (periodicRegion.motif, periodicRegion.period₁, periodicRegion.period₂)
  invFun data :=
    { motif := data.1
      period₁ := data.2.1
      period₂ := data.2.2 }
  left_inv periodicRegion := by cases periodicRegion; rfl
  right_inv data := by rcases data with ⟨motif, period₁, period₂⟩; rfl

instance : Primcodable PeriodicRegion :=
  Primcodable.ofEquiv (List Cell × Cell × Cell) equivData

/-- Determinant of the two period vectors. -/
def determinant (periodicRegion : PeriodicRegion) : Int :=
  periodicRegion.period₁.1 * periodicRegion.period₂.2 -
    periodicRegion.period₁.2 * periodicRegion.period₂.1

/-- The presentation describes a 2D-periodic region precisely when its two
period vectors are linearly independent. -/
def IsFullRank (periodicRegion : PeriodicRegion) : Prop :=
  periodicRegion.determinant ≠ 0

/-- The infinite subset represented by the finite motif and its two periods. -/
def carrier (periodicRegion : PeriodicRegion) : Set Cell :=
  { cell | ∃ base ∈ periodicRegion.motif, ∃ i j : Int,
      cell = Cell.add (Cell.add base (Cell.scale i periodicRegion.period₁))
        (Cell.scale j periodicRegion.period₂) }

end PeriodicRegion

/-- A finite presentation of a 1.5-dimensional periodic subset. The ambient strip
is `ℤ × {0, ..., width - 1}`, and `period` is measured along its unbounded
coordinate. -/
structure PeriodicStrip where
  width : Nat
  period : Nat
  motif : List Cell
  deriving DecidableEq, Repr

namespace PeriodicStrip

/-- Product representation used to obtain the standard computability encoding. -/
def equivData : PeriodicStrip ≃ Nat × Nat × List Cell where
  toFun periodicStrip :=
    (periodicStrip.width, periodicStrip.period, periodicStrip.motif)
  invFun data :=
    { width := data.1
      period := data.2.1
      motif := data.2.2 }
  left_inv periodicStrip := by cases periodicStrip; rfl
  right_inv data := by rcases data with ⟨width, period, motif⟩; rfl

instance : Primcodable PeriodicStrip :=
  Primcodable.ofEquiv (Nat × Nat × List Cell) equivData

/-- Membership in the chosen rectangular fundamental domain of a strip. -/
def InFundamentalDomain (periodicStrip : PeriodicStrip) (cell : Cell) : Prop :=
  0 ≤ cell.1 ∧ cell.1 < (periodicStrip.period : Int) ∧
    0 ≤ cell.2 ∧ cell.2 < (periodicStrip.width : Int)

/-- A well-formed strip has positive width and period, and stores its
motif inside the selected fundamental domain. -/
def IsWellFormed (periodicStrip : PeriodicStrip) : Prop :=
  0 < periodicStrip.width ∧ 0 < periodicStrip.period ∧
    ∀ cell ∈ periodicStrip.motif, periodicStrip.InFundamentalDomain cell

/-- The infinite periodic subset represented by `periodicStrip`. -/
def carrier (periodicStrip : PeriodicStrip) : Set Cell :=
  { cell | 0 ≤ cell.2 ∧ cell.2 < (periodicStrip.width : Int) ∧
      ∃ base ∈ periodicStrip.motif, ∃ i : Int,
        cell = Cell.add base
          (Cell.scale i (((periodicStrip.period : Int), 0) : Cell)) }

end PeriodicStrip

/-- The 2D periodic-subset tiling decision predicate for a fixed tromino.
Dependent-period presentations are defined to be no-instances. -/
def PeriodicTrominoTiling
    (tromino : Tromino) (periodicRegion : PeriodicRegion) : Prop :=
  periodicRegion.IsFullRank ∧ tromino.Tileable periodicRegion.carrier

/-- The 1.5D periodic-subset tiling decision predicate for a fixed tromino.
Malformed strip presentations are defined to be no-instances. -/
def PeriodicStripTrominoTiling
    (tromino : Tromino) (periodicStrip : PeriodicStrip) : Prop :=
  periodicStrip.IsWellFormed ∧ tromino.Tileable periodicStrip.carrier

end LeanTrominoes
