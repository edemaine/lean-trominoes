/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteState
import LeanTrominoes.Assignment
import Mathlib.Tactic.DeriveFintype

/-!
# Sparse finite frontiers for periodic strip tilings

A tromino has horizontal diameter at most three, so local constraints at one
strip column inspect a five-column assignment window.  The state below stores
assignment values only for cells occurring in the finite motif, rather than
for every row below the (binary-encoded) strip width.  Successive windows
advance the horizontal input phase and agree on their four shared columns.

This supplies the finite transition system used in the 1.5D PSPACE upper
bound.  Its equivalence with global strip tilings is proved separately.
-/

namespace LeanTrominoes

namespace PeriodicStrip

abbrev MotifCell (periodicStrip : PeriodicStrip) :=
  ↑periodicStrip.motif.toFinset

def shiftPhase {period : Nat} (phase : Fin period) (displacement : Int) :
    Fin period :=
  ⟨(((phase.val : Int) + displacement) % period).toNat, by
    have periodPositive : (0 : Int) < period := by
      exact_mod_cast Nat.zero_lt_of_lt phase.isLt
    rw [Int.toNat_lt (Int.emod_nonneg _ (by omega))]
    exact Int.emod_lt_of_pos _ periodPositive⟩

/-- Horizontal coordinate reduced to the strip's positive period. -/
def phaseAt (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period) (coordinate : Int) :
    Fin periodicStrip.period :=
  ⟨(coordinate % periodicStrip.period).toNat, by
    rw [Int.toNat_lt (Int.emod_nonneg _ (by omega))]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast periodPositive)⟩

theorem phaseAt_val_int (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period) (coordinate : Int) :
    ((periodicStrip.phaseAt periodPositive coordinate).val : Int) =
      coordinate % periodicStrip.period := by
  rw [phaseAt, Int.toNat_of_nonneg]
  exact Int.emod_nonneg _ (by omega)

@[simp]
theorem phaseAt_add (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (coordinate displacement : Int) :
    periodicStrip.phaseAt periodPositive (coordinate + displacement) =
      shiftPhase (periodicStrip.phaseAt periodPositive coordinate)
        displacement := by
  apply Fin.ext
  simp only [phaseAt, shiftPhase]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg coordinate (by omega))]
  rw [Int.add_emod]
  conv_rhs => rw [Int.add_emod, Int.emod_emod]

@[simp]
theorem shiftPhase_zero {period : Nat} (phase : Fin period) :
    shiftPhase phase 0 = phase := by
  apply Fin.ext
  simp only [shiftPhase, add_zero]
  have nonnegative : (0 : Int) ≤ phase.val := by positivity
  have below : (phase.val : Int) < period := by exact_mod_cast phase.isLt
  rw [Int.emod_eq_of_lt nonnegative below]
  simp

@[simp]
theorem shiftPhase_add {period : Nat} (phase : Fin period)
    (first second : Int) :
    shiftPhase (shiftPhase phase first) second =
      shiftPhase phase (first + second) := by
  apply Fin.ext
  simp only [shiftPhase]
  have periodPositive : (0 : Int) < period := by
    exact_mod_cast Nat.zero_lt_of_lt phase.isLt
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  rw [Int.add_emod]
  rw [Int.emod_emod]
  rw [← Int.add_emod]
  congr 2
  omega

/-- Horizontal congruence modulo the strip period preserves carrier
membership. -/
theorem mem_carrier_congr_x (periodicStrip : PeriodicStrip)
    {first second row : Int}
    (congruent : (periodicStrip.period : Int) ∣ second - first) :
    (first, row) ∈ periodicStrip.carrier ↔
      (second, row) ∈ periodicStrip.carrier := by
  rw [periodicStrip.mem_carrier_iff, periodicStrip.mem_carrier_iff]
  constructor
  · rintro ⟨rowNonnegative, rowBelow, base, baseMem, baseRow, divides⟩
    refine ⟨rowNonnegative, rowBelow, base, baseMem, baseRow, ?_⟩
    have sum := Int.dvd_add congruent divides
    convert sum using 1
    ring
  · rintro ⟨rowNonnegative, rowBelow, base, baseMem, baseRow, divides⟩
    refine ⟨rowNonnegative, rowBelow, base, baseMem, baseRow, ?_⟩
    have reverse : (periodicStrip.period : Int) ∣ first - second := by
      have negated := Int.dvd_neg.mpr congruent
      convert negated using 1
      ring
    have sum := Int.dvd_add reverse divides
    convert sum using 1
    ring

/-- Every coordinate has the same carrier membership as its representative
phase in the fundamental period. -/
theorem mem_carrier_phaseAt_iff (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period) (coordinate row : Int) :
    (coordinate, row) ∈ periodicStrip.carrier ↔
      (((periodicStrip.phaseAt periodPositive coordinate).val : Int), row) ∈
        periodicStrip.carrier := by
  apply periodicStrip.mem_carrier_congr_x
  rw [periodicStrip.phaseAt_val_int periodPositive]
  refine ⟨-(coordinate / periodicStrip.period), ?_⟩
  have division := Int.emod_add_mul_ediv coordinate periodicStrip.period
  ring_nf at division ⊢
  omega

/-- In a well-formed presentation, carrier membership at a fundamental phase
is exactly membership in the finite motif. -/
theorem mem_carrier_phase_iff_mem_motif (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (phase : Fin periodicStrip.period) (row : Int) :
    (((phase.val : Int), row) : Cell) ∈ periodicStrip.carrier ↔
      (((phase.val : Int), row) : Cell) ∈ periodicStrip.motif.toFinset := by
  constructor
  · rw [periodicStrip.mem_carrier_iff]
    rintro ⟨_, _, base, baseMem, baseRow, divides⟩
    have baseDomain := wellFormed.2.2 base baseMem
    have baseNonnegative : 0 ≤ base.1 := baseDomain.1
    have baseBelow : base.1 < (periodicStrip.period : Int) :=
      baseDomain.2.1
    have phaseNonnegative : (0 : Int) ≤ phase.val := by positivity
    have phaseBelow : (phase.val : Int) < periodicStrip.period := by
      exact_mod_cast phase.isLt
    have differenceZero :
        (phase.val : Int) - base.1 = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd divides
      rw [abs_lt]
      constructor <;> omega
    have baseEq : base = (((phase.val : Int), row) : Cell) := by
      apply Prod.ext
      · omega
      · exact baseRow
    simpa [baseEq] using baseMem
  · intro motifMem
    have listMem : (((phase.val : Int), row) : Cell) ∈
        periodicStrip.motif := by
      simpa using motifMem
    have domain := wellFormed.2.2 _ listMem
    rw [periodicStrip.mem_carrier_iff]
    refine ⟨domain.2.2.1, domain.2.2.2,
      ((phase.val : Int), row), listMem, rfl, ?_⟩
    simp

abbrev WindowColumn := Fin 5

def WindowColumn.displacement (column : WindowColumn) : Int :=
  column.val - 2

/-- Interpret an integer displacement in the five-column window. -/
def WindowColumn.ofDisplacement? (displacement : Int) :
    Option WindowColumn :=
  if inside : 0 ≤ displacement + 2 ∧ displacement + 2 < 5 then
    some ⟨(displacement + 2).toNat, by
      rw [Int.toNat_lt inside.1]
      exact inside.2⟩
  else
    none

@[simp]
theorem WindowColumn.ofDisplacement?_displacement (column : WindowColumn) :
    WindowColumn.ofDisplacement? column.displacement = some column := by
  rw [WindowColumn.ofDisplacement?]
  have inside : 0 ≤ column.displacement + 2 ∧
      column.displacement + 2 < 5 := by
    simp [WindowColumn.displacement]
  rw [dif_pos inside]
  apply congrArg some
  apply Fin.ext
  simp [WindowColumn.displacement]

@[simp]
theorem WindowColumn.displacement_succ (column : Fin 4) :
    WindowColumn.displacement (column.succ : WindowColumn) =
      WindowColumn.displacement (column.castSucc : WindowColumn) + 1 := by
  simp [WindowColumn.displacement]
  omega

structure WindowState (periodicStrip : PeriodicStrip) where
  phase : Fin periodicStrip.period
  assignment :
    WindowColumn → periodicStrip.MotifCell → Option SquareSymmetry
  deriving DecidableEq, Fintype

namespace WindowState

def columnPhase {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) (column : WindowColumn) :
    Fin periodicStrip.period :=
  shiftPhase state.phase column.displacement

def center : WindowColumn := ⟨2, by omega⟩

@[simp]
theorem center_displacement :
    center.displacement = 0 := by
  rfl

@[simp]
theorem columnPhase_center {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) :
    state.columnPhase center = state.phase := by
  simp [columnPhase]

/-- Assignment value at a row of one window column.  A missing motif cell is
necessarily outside the represented strip region and receives `none`. -/
def valueAt {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) (column : WindowColumn) (row : Int) :
    Option SquareSymmetry :=
  let cell : Cell := ((state.columnPhase column).val, row)
  if cell_mem : cell ∈ periodicStrip.motif.toFinset then
    state.assignment column ⟨cell, cell_mem⟩
  else
    none

/-- Interpret a window state as an assignment on coordinates relative to its
center column, using `none` beyond the five stored columns. -/
def localAssignment {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) : TrominoAssignment :=
  fun offset =>
    match WindowColumn.ofDisplacement? offset.1 with
    | some column => state.valueAt column offset.2
    | none => none

/-- Region membership in coordinates relative to the representative center
whose horizontal coordinate is `state.phase`. -/
def RelativeRegion {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) : Set Cell :=
  { cell |
    (((state.phase.val : Int) + cell.1, cell.2) : Cell) ∈
      periodicStrip.carrier }

def IsNormalized {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) : Prop :=
  ∀ column base,
    ((base.val.1 : Int) = (state.columnPhase column).val) ∨
      state.assignment column base = none

/-- The local tiling constraints whose distinguished offset and target cell
lie in the center column of a window. -/
def IsCenterValid (tromino : Tromino) {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) : Prop :=
  (∀ base : periodicStrip.MotifCell,
      base.val.1 = (state.phase.val : Int) →
      ∀ symmetry,
        state.assignment center base = some symmetry →
        ∀ cell ∈
            (Placement.mk () symmetry (0, base.val.2)).cells
              (fun _ : Unit => tromino.cells),
          cell ∈ state.RelativeRegion) ∧
    ∀ base : periodicStrip.MotifCell,
      base.val.1 = (state.phase.val : Int) →
      ((TrominoAssignment.coveringPlacements
          tromino (0, base.val.2)).filter fun placement =>
        state.localAssignment placement.offset =
          some placement.symmetry).card = 1

def Overlaps {periodicStrip : PeriodicStrip}
    (current next : WindowState periodicStrip) : Prop :=
  next.phase = shiftPhase current.phase 1 ∧
    ∀ column : Fin 4, ∀ base,
      current.assignment column.succ base =
        next.assignment column.castSucc base

/-- One transition checks the departing window, advances the periodic phase,
and shifts the four shared columns consistently. -/
def Transition (tromino : Tromino) {periodicStrip : PeriodicStrip}
    (current next : WindowState periodicStrip) : Prop :=
  current.IsNormalized ∧ current.IsCenterValid tromino ∧
    current.Overlaps next

instance {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) : Decidable state.IsNormalized := by
  unfold IsNormalized
  infer_instance

instance (tromino : Tromino) {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) :
    Decidable (state.IsCenterValid tromino) := by
  unfold IsCenterValid RelativeRegion
  infer_instance

instance {periodicStrip : PeriodicStrip}
    (current next : WindowState periodicStrip) :
    Decidable (current.Overlaps next) := by
  unfold Overlaps
  infer_instance

instance (tromino : Tromino) {periodicStrip : PeriodicStrip}
    (current next : WindowState periodicStrip) :
    Decidable (Transition tromino current next) := by
  unfold Transition
  infer_instance

theorem columnPhase_overlap {periodicStrip : PeriodicStrip}
    (current next : WindowState periodicStrip)
    (overlaps : current.Overlaps next) (column : Fin 4) :
    current.columnPhase column.succ =
      next.columnPhase column.castSucc := by
  rw [columnPhase, columnPhase, overlaps.1]
  rw [shiftPhase_add]
  congr 1
  rw [WindowColumn.displacement_succ]
  omega

end WindowState
end PeriodicStrip
end LeanTrominoes
