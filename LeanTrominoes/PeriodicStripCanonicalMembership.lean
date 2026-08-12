import LeanTrominoes.StripFrontierPacked

/-!
# Canonical motif representatives in a periodic strip

For a well-formed strip, every carrier cell has a unique horizontal
representative in the fundamental domain.  These lemmas identify carrier
membership with membership of that representative in the finite motif and
specialize the result to packed frontier columns.
-/

namespace LeanTrominoes
namespace PeriodicStrip

/-- A fundamental-domain representative congruent to a cell's horizontal
coordinate belongs to the finite motif exactly when the cell belongs to the
infinite strip carrier. -/
theorem mem_carrier_iff_mem_motif_of_congruent
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (x y : Int) (canonical : Nat)
    (canonicalBelow : canonical < periodicStrip.period)
    (congruent : (periodicStrip.period : Int) ∣
      x - (canonical : Int)) :
    (x, y) ∈ periodicStrip.carrier ↔
      (((canonical : Int), y) : Cell) ∈ periodicStrip.motif := by
  rw [periodicStrip.mem_carrier_iff]
  constructor
  · rintro ⟨_yNonnegative, _yBelow, base, baseMember,
      baseY, baseCongruent⟩
    have baseDomain := wellFormed.2.2 base baseMember
    have canonicalNonnegative : 0 ≤ (canonical : Int) := by omega
    have canonicalBelowInt :
        (canonical : Int) < periodicStrip.period := by
      exact_mod_cast canonicalBelow
    have representativeDivides :
        (periodicStrip.period : Int) ∣
          (canonical : Int) - base.1 := by
      have difference :
          (periodicStrip.period : Int) ∣
            (x - base.1) - (x - (canonical : Int)) :=
        baseCongruent.sub congruent
      have differenceEq :
          (x - base.1) - (x - (canonical : Int)) =
            (canonical : Int) - base.1 := by
        ring
      rw [differenceEq] at difference
      exact difference
    have baseXNonnegative : 0 ≤ base.1 := baseDomain.1
    have baseXBelow : base.1 < (periodicStrip.period : Int) :=
      baseDomain.2.1
    have representativeAbs :
        |(canonical : Int) - base.1| < periodicStrip.period := by
      rw [abs_lt]
      constructor <;> omega
    have representativeZero :
        (canonical : Int) - base.1 = 0 :=
      Int.eq_zero_of_abs_lt_dvd
        representativeDivides representativeAbs
    have baseX : base.1 = (canonical : Int) := by omega
    have baseEq : base = (((canonical : Int), y) : Cell) := by
      apply Prod.ext
      · exact baseX
      · exact baseY
    simpa [baseEq] using baseMember
  · intro canonicalMember
    have canonicalDomain :=
      wellFormed.2.2
        (((canonical : Int), y) : Cell) canonicalMember
    exact ⟨canonicalDomain.2.2.1, canonicalDomain.2.2.2,
      (((canonical : Int), y) : Cell), canonicalMember,
      rfl, congruent⟩

/-- Boolean form of `mem_carrier_iff_mem_motif_of_congruent`. -/
theorem contains_eq_true_iff_mem_motif_of_congruent
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (x y : Int) (canonical : Nat)
    (canonicalBelow : canonical < periodicStrip.period)
    (congruent : (periodicStrip.period : Int) ∣
      x - (canonical : Int)) :
    periodicStrip.contains (x, y) = true ↔
      (((canonical : Int), y) : Cell) ∈ periodicStrip.motif := by
  exact (periodicStrip.contains_eq_true_iff (x, y)).trans
    (mem_carrier_iff_mem_motif_of_congruent periodicStrip
      wellFormed x y canonical canonicalBelow congruent)

namespace PackedWindowState

theorem columnPhase_lt
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (column : WindowColumn) :
    packed.columnPhase periodicStrip column < periodicStrip.period := by
  exact Nat.mod_lt _ wellFormed.2.1

/-- The physical horizontal coordinate represented by a packed column is
congruent modulo the strip period to the column's canonical phase. -/
theorem columnPhase_congruent
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (column : WindowColumn) :
    (periodicStrip.period : Int) ∣
      ((packed.phase : Int) + column.displacement) -
        (packed.columnPhase periodicStrip column : Int) := by
  let total :=
    packed.phase + column.val + 2 * periodicStrip.period
  let numerator := total - 2
  have periodPositive : 0 < periodicStrip.period := wellFormed.2.1
  have twoLeTotal : 2 ≤ total := by
    simp only [total]
    omega
  have numeratorCast :
      (numerator : Int) =
        (packed.phase : Int) + column.val +
          2 * periodicStrip.period - 2 := by
    simp only [numerator]
    rw [Int.ofNat_sub twoLeTotal]
    simp only [total]
    push_cast
    ring
  have divisionIdentity :
      (numerator : Int) =
        (numerator % periodicStrip.period : Nat) +
          (periodicStrip.period : Int) *
            (numerator / periodicStrip.period : Nat) := by
    exact_mod_cast (Nat.mod_add_div numerator periodicStrip.period).symm
  refine ⟨((numerator / periodicStrip.period : Nat) : Int) - 2, ?_⟩
  unfold WindowColumn.displacement PackedWindowState.columnPhase
  have numeratorEq :
      packed.phase + column.val + 2 * periodicStrip.period - 2 =
        numerator := by
    rfl
  rw [numeratorEq]
  ring_nf
  omega

/-- Packed-column specialization: the infinite membership test equals finite
motif membership of the column's canonical representative. -/
theorem contains_column_eq_true_iff_mem_motif
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (column : WindowColumn)
    (row : Int) :
    periodicStrip.contains
        ((packed.phase : Int) + column.displacement, row) = true ↔
      ((((packed.columnPhase periodicStrip column : Nat) : Int), row) :
        Cell) ∈ periodicStrip.motif := by
  exact contains_eq_true_iff_mem_motif_of_congruent
    periodicStrip wellFormed
    ((packed.phase : Int) + column.displacement) row
    (packed.columnPhase periodicStrip column)
    (columnPhase_lt periodicStrip wellFormed packed column)
    (columnPhase_congruent periodicStrip wellFormed packed column)

/-- The same bridge stated for the coordinatewise cell addition used by the
center-containment specification. -/
theorem contains_add_eq_true_iff_mem_motif
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (column : WindowColumn)
    (row : Int) (offset : Cell)
    (horizontal : offset.1 = column.displacement) :
    periodicStrip.contains
        (Cell.add ((packed.phase : Int), row) offset) = true ↔
      ((((packed.columnPhase periodicStrip column : Nat) : Int),
        row + offset.2) : Cell) ∈ periodicStrip.motif := by
  simpa [Cell.add, horizontal] using
    contains_column_eq_true_iff_mem_motif
      periodicStrip wellFormed packed column (row + offset.2)

end PackedWindowState

end PeriodicStrip
end LeanTrominoes
