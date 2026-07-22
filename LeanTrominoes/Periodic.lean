import LeanTrominoes.Tiling
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic.Ring

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

instance (periodicRegion : PeriodicRegion) : Decidable periodicRegion.IsFullRank := by
  unfold IsFullRank
  infer_instance

/-- Numerator of the first coordinate in Cramer's rule for the period basis. -/
def firstNumerator (periodicRegion : PeriodicRegion) (cell : Cell) : Int :=
  cell.1 * periodicRegion.period₂.2 - cell.2 * periodicRegion.period₂.1

/-- Numerator of the second coordinate in Cramer's rule for the period basis. -/
def secondNumerator (periodicRegion : PeriodicRegion) (cell : Cell) : Int :=
  periodicRegion.period₁.1 * cell.2 - periodicRegion.period₁.2 * cell.1

/-- Executable test for membership in the integer span of the two period
vectors. It characterizes that span when the presentation has full rank. -/
def latticeContains (periodicRegion : PeriodicRegion) (cell : Cell) : Bool :=
  decide (periodicRegion.determinant ∣ periodicRegion.firstNumerator cell) &&
    decide (periodicRegion.determinant ∣ periodicRegion.secondNumerator cell)

theorem latticeContains_eq_true_iff (periodicRegion : PeriodicRegion)
    (full_rank : periodicRegion.IsFullRank) (cell : Cell) :
    periodicRegion.latticeContains cell = true ↔
      ∃ i j : Int,
        cell = Cell.add (Cell.scale i periodicRegion.period₁)
          (Cell.scale j periodicRegion.period₂) := by
  constructor
  · intro contains
    simp only [latticeContains, Bool.and_eq_true, decide_eq_true_eq] at contains
    obtain ⟨⟨i, first_eq⟩, ⟨j, second_eq⟩⟩ := contains
    refine ⟨i, j, ?_⟩
    apply Prod.ext
    · simp only [Cell.add, Cell.scale]
      apply mul_left_cancel₀ full_rank
      calc
        periodicRegion.determinant * cell.1 =
            periodicRegion.firstNumerator cell * periodicRegion.period₁.1 +
              periodicRegion.secondNumerator cell * periodicRegion.period₂.1 := by
                simp only [determinant, firstNumerator, secondNumerator]
                ring
        _ = (periodicRegion.determinant * i) * periodicRegion.period₁.1 +
              (periodicRegion.determinant * j) * periodicRegion.period₂.1 := by
                rw [first_eq, second_eq]
        _ = periodicRegion.determinant *
              (i * periodicRegion.period₁.1 + j * periodicRegion.period₂.1) := by
                ring
    · simp only [Cell.add, Cell.scale]
      apply mul_left_cancel₀ full_rank
      calc
        periodicRegion.determinant * cell.2 =
            periodicRegion.firstNumerator cell * periodicRegion.period₁.2 +
              periodicRegion.secondNumerator cell * periodicRegion.period₂.2 := by
                simp only [determinant, firstNumerator, secondNumerator]
                ring
        _ = (periodicRegion.determinant * i) * periodicRegion.period₁.2 +
              (periodicRegion.determinant * j) * periodicRegion.period₂.2 := by
                rw [first_eq, second_eq]
        _ = periodicRegion.determinant *
              (i * periodicRegion.period₁.2 + j * periodicRegion.period₂.2) := by
                ring
  · rintro ⟨i, j, rfl⟩
    simp only [latticeContains, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · refine ⟨i, ?_⟩
      simp only [determinant, firstNumerator, Cell.add, Cell.scale]
      ring
    · refine ⟨j, ?_⟩
      simp only [determinant, secondNumerator, Cell.add, Cell.scale]
      ring

/-- The infinite subset represented by the finite motif and its two periods. -/
def carrier (periodicRegion : PeriodicRegion) : Set Cell :=
  { cell | ∃ base ∈ periodicRegion.motif, ∃ i j : Int,
      cell = Cell.add (Cell.add base (Cell.scale i periodicRegion.period₁))
        (Cell.scale j periodicRegion.period₂) }

/-- Executable membership check for a full-rank two-dimensional periodic
presentation. -/
def contains (periodicRegion : PeriodicRegion) (cell : Cell) : Bool :=
  periodicRegion.motif.any fun base =>
    periodicRegion.latticeContains (cell.1 - base.1, cell.2 - base.2)

theorem contains_eq_true_iff (periodicRegion : PeriodicRegion)
    (full_rank : periodicRegion.IsFullRank) (cell : Cell) :
    periodicRegion.contains cell = true ↔ cell ∈ periodicRegion.carrier := by
  constructor
  · intro contains_true
    simp only [PeriodicRegion.contains, List.any_eq_true] at contains_true
    obtain ⟨base, base_mem, lattice_mem⟩ := contains_true
    obtain ⟨i, j, displacement⟩ :=
      (periodicRegion.latticeContains_eq_true_iff full_rank _).mp lattice_mem
    refine ⟨base, base_mem, i, j, ?_⟩
    apply Prod.ext
    · have x_displacement := congrArg Prod.fst displacement
      simp only [Cell.add, Cell.scale] at x_displacement ⊢
      calc
        cell.1 = base.1 + (cell.1 - base.1) := by ring
        _ = base.1 +
            (i * periodicRegion.period₁.1 + j * periodicRegion.period₂.1) := by
              rw [x_displacement]
        _ = base.1 + i * periodicRegion.period₁.1 +
            j * periodicRegion.period₂.1 := by ring
    · have y_displacement := congrArg Prod.snd displacement
      simp only [Cell.add, Cell.scale] at y_displacement ⊢
      calc
        cell.2 = base.2 + (cell.2 - base.2) := by ring
        _ = base.2 +
            (i * periodicRegion.period₁.2 + j * periodicRegion.period₂.2) := by
              rw [y_displacement]
        _ = base.2 + i * periodicRegion.period₁.2 +
            j * periodicRegion.period₂.2 := by ring
  · rintro ⟨base, base_mem, i, j, equality⟩
    simp only [PeriodicRegion.contains, List.any_eq_true]
    refine ⟨base, base_mem, ?_⟩
    apply (periodicRegion.latticeContains_eq_true_iff full_rank _).mpr
    refine ⟨i, j, ?_⟩
    apply Prod.ext
    · have x_equality := congrArg Prod.fst equality
      simp only [Cell.add, Cell.scale] at x_equality ⊢
      rw [x_equality]
      ring
    · have y_equality := congrArg Prod.snd equality
      simp only [Cell.add, Cell.scale] at y_equality ⊢
      rw [y_equality]
      ring

/-- Executable test that rejects a dependent period presentation and otherwise
tests carrier membership. -/
def validContains (periodicRegion : PeriodicRegion) (cell : Cell) : Bool :=
  decide periodicRegion.IsFullRank && periodicRegion.contains cell

theorem validContains_eq_true_iff (periodicRegion : PeriodicRegion) (cell : Cell) :
    periodicRegion.validContains cell = true ↔
      periodicRegion.IsFullRank ∧ cell ∈ periodicRegion.carrier := by
  rw [validContains, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨full_rank, contains_true⟩
    exact ⟨full_rank,
      (periodicRegion.contains_eq_true_iff full_rank cell).mp contains_true⟩
  · rintro ⟨full_rank, cell_mem⟩
    exact ⟨full_rank,
      (periodicRegion.contains_eq_true_iff full_rank cell).mpr cell_mem⟩

instance (periodicRegion : PeriodicRegion) (cell : Cell) :
    Decidable (periodicRegion.IsFullRank ∧ cell ∈ periodicRegion.carrier) :=
  decidable_of_iff (periodicRegion.validContains cell = true)
    (periodicRegion.validContains_eq_true_iff cell)

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

instance (periodicStrip : PeriodicStrip) (cell : Cell) :
    Decidable (periodicStrip.InFundamentalDomain cell) := by
  unfold InFundamentalDomain
  infer_instance

/-- A well-formed strip has positive width and period, and stores its
motif inside the selected fundamental domain. -/
def IsWellFormed (periodicStrip : PeriodicStrip) : Prop :=
  0 < periodicStrip.width ∧ 0 < periodicStrip.period ∧
    ∀ cell ∈ periodicStrip.motif, periodicStrip.InFundamentalDomain cell

/-- Executable well-formedness check for a strip presentation. -/
def wellFormed (periodicStrip : PeriodicStrip) : Bool :=
  decide (0 < periodicStrip.width) &&
    decide (0 < periodicStrip.period) &&
    periodicStrip.motif.all fun cell =>
      decide (periodicStrip.InFundamentalDomain cell)

theorem wellFormed_eq_true_iff (periodicStrip : PeriodicStrip) :
    periodicStrip.wellFormed = true ↔ periodicStrip.IsWellFormed := by
  simp [wellFormed, IsWellFormed, and_assoc]

instance (periodicStrip : PeriodicStrip) : Decidable periodicStrip.IsWellFormed :=
  decidable_of_iff (periodicStrip.wellFormed = true)
    periodicStrip.wellFormed_eq_true_iff

/-- The infinite periodic subset represented by `periodicStrip`. -/
def carrier (periodicStrip : PeriodicStrip) : Set Cell :=
  { cell | 0 ≤ cell.2 ∧ cell.2 < (periodicStrip.width : Int) ∧
      ∃ base ∈ periodicStrip.motif, ∃ i : Int,
        cell = Cell.add base
          (Cell.scale i (((periodicStrip.period : Int), 0) : Cell)) }

/-- Arithmetic characterization of membership in a periodic strip. -/
theorem mem_carrier_iff (periodicStrip : PeriodicStrip) (cell : Cell) :
    cell ∈ periodicStrip.carrier ↔
      0 ≤ cell.2 ∧ cell.2 < (periodicStrip.width : Int) ∧
        ∃ base ∈ periodicStrip.motif,
          base.2 = cell.2 ∧
            (periodicStrip.period : Int) ∣ cell.1 - base.1 := by
  constructor
  · rintro ⟨nonnegative, below_width, base, base_mem, i, equality⟩
    refine ⟨nonnegative, below_width, base, base_mem, ?_, ?_⟩
    · have y_equality := congrArg Prod.snd equality
      simpa [Cell.add, Cell.scale] using y_equality.symm
    · refine ⟨i, ?_⟩
      have x_equality := congrArg Prod.fst equality
      simp only [Cell.add, Cell.scale] at x_equality
      calc
        cell.1 - base.1 =
            (base.1 + i * (periodicStrip.period : Int)) - base.1 := by
              rw [x_equality]
        _ = (periodicStrip.period : Int) * i := by ring
  · rintro ⟨nonnegative, below_width, base, base_mem, y_equality, i, x_equality⟩
    refine ⟨nonnegative, below_width, base, base_mem, i, ?_⟩
    apply Prod.ext
    · simp only [Cell.add, Cell.scale]
      calc
        cell.1 = base.1 + (cell.1 - base.1) := by ring
        _ = base.1 + (periodicStrip.period : Int) * i := by rw [x_equality]
        _ = base.1 + i * (periodicStrip.period : Int) := by ring
    · simp only [Cell.add, Cell.scale, mul_zero, add_zero]
      exact y_equality.symm

/-- Executable membership check for the infinite carrier of a strip
presentation. -/
def contains (periodicStrip : PeriodicStrip) (cell : Cell) : Bool :=
  decide (0 ≤ cell.2) &&
    decide (cell.2 < (periodicStrip.width : Int)) &&
    periodicStrip.motif.any fun base =>
      decide (base.2 = cell.2) &&
        decide ((periodicStrip.period : Int) ∣ cell.1 - base.1)

theorem contains_eq_true_iff (periodicStrip : PeriodicStrip) (cell : Cell) :
    periodicStrip.contains cell = true ↔ cell ∈ periodicStrip.carrier := by
  rw [periodicStrip.mem_carrier_iff]
  simp [contains, and_assoc]

instance (periodicStrip : PeriodicStrip) (cell : Cell) :
    Decidable (cell ∈ periodicStrip.carrier) :=
  decidable_of_iff (periodicStrip.contains cell = true)
    (periodicStrip.contains_eq_true_iff cell)

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
