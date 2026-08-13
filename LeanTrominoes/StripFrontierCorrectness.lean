/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StripFrontier

/-!
# Correctness of sparse periodic strip frontiers

This file connects the finite five-column frontier system to the global local
constraint formulation of tromino tilings.  The forward direction proved here
cuts any globally valid assignment into a bi-infinite path of sparse frontier
states.  The converse reconstruction is developed in the same interface.
-/

namespace LeanTrominoes.PeriodicStrip.WindowState

/-- Five-column window cut from a global assignment. -/
def ofAssignment {periodicStrip : PeriodicStrip}
    (periodPositive : 0 < periodicStrip.period)
    (assignment : TrominoAssignment) (coordinate : Int) :
    WindowState periodicStrip where
  phase := periodicStrip.phaseAt periodPositive coordinate
  assignment column base :=
    if _baseAtPhase :
        base.val.1 =
          ((periodicStrip.phaseAt periodPositive
            (coordinate + column.displacement)).val : Int) then
      assignment (coordinate + column.displacement, base.val.2)
    else
      none

@[simp]
theorem ofAssignment_phase {periodicStrip : PeriodicStrip}
    (periodPositive : 0 < periodicStrip.period)
    (assignment : TrominoAssignment) (coordinate : Int) :
    (ofAssignment periodPositive assignment coordinate).phase =
      periodicStrip.phaseAt periodPositive coordinate := by
  rfl

theorem ofAssignment_columnPhase {periodicStrip : PeriodicStrip}
    (periodPositive : 0 < periodicStrip.period)
    (assignment : TrominoAssignment) (coordinate : Int)
    (column : WindowColumn) :
    (ofAssignment periodPositive assignment coordinate).columnPhase column =
      periodicStrip.phaseAt periodPositive
        (coordinate + column.displacement) := by
  rw [columnPhase, ofAssignment_phase, periodicStrip.phaseAt_add]

theorem ofAssignment_isNormalized {periodicStrip : PeriodicStrip}
    (periodPositive : 0 < periodicStrip.period)
    (assignment : TrominoAssignment) (coordinate : Int) :
    (ofAssignment periodPositive assignment coordinate).IsNormalized := by
  intro column base
  rw [ofAssignment_columnPhase]
  by_cases baseAtPhase :
      base.val.1 =
        ((periodicStrip.phaseAt periodPositive
          (coordinate + column.displacement)).val : Int)
  · exact Or.inl baseAtPhase
  · right
    change (if base.val.1 =
        ((periodicStrip.phaseAt periodPositive
          (coordinate + column.displacement)).val : Int) then
      assignment (coordinate + column.displacement, base.val.2)
    else none) = none
    rw [if_neg baseAtPhase]

theorem ofAssignment_overlaps {periodicStrip : PeriodicStrip}
    (periodPositive : 0 < periodicStrip.period)
    (assignment : TrominoAssignment) (coordinate : Int) :
    (ofAssignment periodPositive assignment coordinate).Overlaps
      (ofAssignment periodPositive assignment (coordinate + 1)) := by
  constructor
  · rw [ofAssignment_phase, ofAssignment_phase,
      periodicStrip.phaseAt_add]
  · intro column base
    simp only [ofAssignment]
    have displacement :
        coordinate +
            WindowColumn.displacement (column.succ : WindowColumn) =
          coordinate + 1 +
            WindowColumn.displacement (column.castSucc : WindowColumn) := by
      rw [WindowColumn.displacement_succ]
      omega
    rw [displacement]

/-- Every placement that can cover a cell has its horizontal offset within
two columns of that cell. -/
theorem candidate_offset_x_bounds (tromino : Tromino) (cell : Cell)
    (placement : Placement Unit)
    (candidate :
      placement ∈ TrominoAssignment.coveringPlacements tromino cell) :
    cell.1 - 2 ≤ placement.offset.1 ∧
      placement.offset.1 ≤ cell.1 + 2 := by
  rw [TrominoAssignment.coveringPlacements, Finset.mem_image] at candidate
  obtain ⟨⟨symmetry, source⟩, sourceData, rfl⟩ := candidate
  have sourceMem : source ∈ tromino.cells :=
    (Finset.mem_product.mp sourceData).2
  cases tromino <;> cases symmetry <;>
    simp [Tromino.cells, SquareSymmetry.act, Cell.sub] at sourceMem ⊢ <;>
    rcases sourceMem with (rfl | rfl | rfl) <;> omega

/-- Local validity forces every assignment offset outside the region to be
inactive. -/
theorem assignment_eq_none_of_not_mem (tromino : Tromino)
    {region : Set Cell} {assignment : TrominoAssignment}
    (valid : assignment.IsLocallyValid tromino region)
    {offset : Cell} (outside : offset ∉ region) :
    assignment offset = none := by
  cases selected : assignment offset with
  | none => rfl
  | some symmetry =>
      exfalso
      apply outside
      exact valid.1 offset symmetry selected offset
        (tromino.offset_mem_placement_cells
          (Placement.mk () symmetry offset))

/-- A window cut from a valid global assignment reproduces that assignment
at every stored horizontal displacement. -/
theorem ofAssignment_valueAt (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    {assignment : TrominoAssignment}
    (valid :
      assignment.IsLocallyValid tromino periodicStrip.carrier)
    (coordinate : Int) (column : WindowColumn) (row : Int) :
    (ofAssignment wellFormed.2.1 assignment coordinate).valueAt column row =
      assignment (coordinate + column.displacement, row) := by
  rw [valueAt]
  rw [ofAssignment_columnPhase]
  let phase :=
    periodicStrip.phaseAt wellFormed.2.1
      (coordinate + column.displacement)
  let representative : Cell := ((phase.val : Int), row)
  change (if representativeMem :
      representative ∈ periodicStrip.motif.toFinset then
    (ofAssignment wellFormed.2.1 assignment coordinate).assignment column
      ⟨representative, representativeMem⟩
  else none) = _
  by_cases representativeMem :
      representative ∈ periodicStrip.motif.toFinset
  · rw [dif_pos representativeMem]
    change (if _ : representative.1 = (phase.val : Int) then
      assignment (coordinate + column.displacement, representative.2)
    else none) = _
    have samePhase : representative.1 = (phase.val : Int) := by
      simp [representative]
    rw [dif_pos samePhase]
  · rw [dif_neg representativeMem]
    apply Eq.symm
    apply assignment_eq_none_of_not_mem tromino valid
    intro actualMem
    have representativeCarrier :
        representative ∈ periodicStrip.carrier :=
      (periodicStrip.mem_carrier_phaseAt_iff
        wellFormed.2.1 (coordinate + column.displacement) row).mp actualMem
    exact representativeMem
      ((periodicStrip.mem_carrier_phase_iff_mem_motif
        wellFormed phase row).mp representativeCarrier)

/-- Consequently the relative assignment read from a valid global window is
the translated global assignment throughout the five-column window. -/
theorem ofAssignment_localAssignment (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    {assignment : TrominoAssignment}
    (valid :
      assignment.IsLocallyValid tromino periodicStrip.carrier)
    (coordinate : Int) (column : WindowColumn) (row : Int) :
    (ofAssignment wellFormed.2.1 assignment coordinate).localAssignment
        (column.displacement, row) =
      assignment (coordinate + column.displacement, row) := by
  rw [localAssignment,
    WindowColumn.ofDisplacement?_displacement]
  exact ofAssignment_valueAt tromino wellFormed valid coordinate column row

/-- Every displacement between `-2` and `2` is represented by a unique
five-window column. -/
theorem exists_windowColumn_of_bounds {displacement : Int}
    (lower : -2 ≤ displacement) (upper : displacement ≤ 2) :
    ∃ column : WindowColumn, column.displacement = displacement := by
  let column : WindowColumn :=
    ⟨(displacement + 2).toNat, by
      rw [Int.toNat_lt (by omega)]
      omega⟩
  refine ⟨column, ?_⟩
  rw [WindowColumn.displacement]
  change (((displacement + 2).toNat : Nat) : Int) - 2 = displacement
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- Coordinate form of `ofAssignment_localAssignment`. -/
theorem ofAssignment_localAssignment_of_bounds (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    {assignment : TrominoAssignment}
    (valid :
      assignment.IsLocallyValid tromino periodicStrip.carrier)
    (coordinate displacement row : Int)
    (lower : -2 ≤ displacement) (upper : displacement ≤ 2) :
    (ofAssignment wellFormed.2.1 assignment coordinate).localAssignment
        (displacement, row) =
      assignment (coordinate + displacement, row) := by
  obtain ⟨column, rfl⟩ :=
    exists_windowColumn_of_bounds lower upper
  exact ofAssignment_localAssignment tromino wellFormed valid
    coordinate column row

/-- Translate a placement horizontally. -/
def translatePlacement (coordinate : Int) (placement : Placement Unit) :
    Placement Unit :=
  { placement with
    offset := (coordinate + placement.offset.1, placement.offset.2) }

@[simp]
theorem translatePlacement_symmetry (coordinate : Int)
    (placement : Placement Unit) :
    (translatePlacement coordinate placement).symmetry =
      placement.symmetry := by
  rfl

@[simp]
theorem translatePlacement_offset (coordinate : Int)
    (placement : Placement Unit) :
    (translatePlacement coordinate placement).offset =
      (coordinate + placement.offset.1, placement.offset.2) := by
  rfl

/-- Horizontal translation bijects the candidates covering corresponding
cells. -/
theorem translatePlacement_mem_coveringPlacements_iff
    (tromino : Tromino) (coordinate : Int) (cell : Cell)
    (placement : Placement Unit) :
    translatePlacement coordinate placement ∈
        TrominoAssignment.coveringPlacements tromino
          (coordinate + cell.1, cell.2) ↔
      placement ∈ TrominoAssignment.coveringPlacements tromino cell := by
  rw [TrominoAssignment.mem_coveringPlacements_iff,
    TrominoAssignment.mem_coveringPlacements_iff]
  simp only [Placement.mem_cells_iff]
  constructor
  · rintro ⟨source, sourceMem, equality⟩
    refine ⟨source, sourceMem, ?_⟩
    apply Prod.ext
    · have xEquality := congrArg Prod.fst equality
      simp only [translatePlacement, Cell.add] at xEquality ⊢
      omega
    · have yEquality := congrArg Prod.snd equality
      simpa only [translatePlacement, Cell.add] using yEquality
  · rintro ⟨source, sourceMem, equality⟩
    refine ⟨source, sourceMem, ?_⟩
    apply Prod.ext
    · have xEquality := congrArg Prod.fst equality
      simp only [translatePlacement, Cell.add] at xEquality ⊢
      omega
    · have yEquality := congrArg Prod.snd equality
      simpa only [translatePlacement, Cell.add] using yEquality

@[simp]
theorem translatePlacement_zero (placement : Placement Unit) :
    translatePlacement 0 placement = placement := by
  cases placement
  simp [translatePlacement]

@[simp]
theorem translatePlacement_neg (coordinate : Int)
    (placement : Placement Unit) :
    translatePlacement (-coordinate)
      (translatePlacement coordinate placement) = placement := by
  cases placement
  simp [translatePlacement]

/-- Translating a valid global assignment into a window preserves the number
of active candidates at a center-column cell. -/
theorem ofAssignment_activeCandidateCount (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    {assignment : TrominoAssignment}
    (valid :
      assignment.IsLocallyValid tromino periodicStrip.carrier)
    (coordinate row : Int) :
    ((TrominoAssignment.coveringPlacements tromino (0, row)).filter
        fun placement =>
          (ofAssignment wellFormed.2.1 assignment coordinate).localAssignment
              placement.offset =
            some placement.symmetry).card =
      ((TrominoAssignment.coveringPlacements
          tromino (coordinate, row)).filter fun placement =>
        assignment placement.offset = some placement.symmetry).card := by
  let localActive :=
    (TrominoAssignment.coveringPlacements tromino (0, row)).filter
      fun placement =>
        (ofAssignment wellFormed.2.1 assignment coordinate).localAssignment
            placement.offset =
          some placement.symmetry
  let globalActive :=
    (TrominoAssignment.coveringPlacements
      tromino (coordinate, row)).filter fun placement =>
        assignment placement.offset = some placement.symmetry
  have activeEq :
      globalActive = localActive.image (translatePlacement coordinate) := by
    ext placement
    constructor
    · intro placementMem
      have placementData := Finset.mem_filter.mp placementMem
      let localPlacement := translatePlacement (-coordinate) placement
      have translateLocal :
          translatePlacement coordinate localPlacement = placement := by
        simp [localPlacement, translatePlacement]
      apply Finset.mem_image.mpr
      refine ⟨localPlacement, ?_, translateLocal⟩
      apply Finset.mem_filter.mpr
      have localCandidate :
          localPlacement ∈
            TrominoAssignment.coveringPlacements tromino (0, row) := by
        rw [← translatePlacement_mem_coveringPlacements_iff
          tromino coordinate (0, row)]
        simpa [translateLocal] using placementData.1
      refine ⟨localCandidate, ?_⟩
      have bounds :=
        candidate_offset_x_bounds tromino (0, row)
          localPlacement localCandidate
      rw [ofAssignment_localAssignment_of_bounds tromino wellFormed valid
        coordinate localPlacement.offset.1 localPlacement.offset.2
          (by omega) (by omega)]
      change assignment (translatePlacement coordinate localPlacement).offset =
        some (translatePlacement coordinate localPlacement).symmetry
      simpa [translateLocal] using placementData.2
    · rw [Finset.mem_image]
      rintro ⟨localPlacement, localMem, rfl⟩
      have localData := Finset.mem_filter.mp localMem
      apply Finset.mem_filter.mpr
      refine ⟨by
        simpa using
          (translatePlacement_mem_coveringPlacements_iff
            tromino coordinate (0, row) localPlacement).mpr localData.1, ?_⟩
      have bounds :=
        candidate_offset_x_bounds tromino (0, row)
          localPlacement localData.1
      change assignment
        (coordinate + localPlacement.offset.1, localPlacement.offset.2) =
          some localPlacement.symmetry
      rw [← ofAssignment_localAssignment_of_bounds tromino wellFormed valid
        coordinate localPlacement.offset.1 localPlacement.offset.2
          (by omega) (by omega)]
      simpa using localData.2
  change localActive.card = globalActive.card
  rw [activeEq, Finset.card_image_of_injective]
  intro first second equality
  have inverseEquality :=
    congrArg (translatePlacement (-coordinate)) equality
  simpa using inverseEquality

/-- Relative region membership in a window cut at `coordinate` is exactly
global carrier membership after translating by `coordinate`. -/
theorem ofAssignment_mem_relativeRegion_iff
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    (assignment : TrominoAssignment) (coordinate : Int) (cell : Cell) :
    cell ∈
        (ofAssignment wellFormed.2.1 assignment coordinate).RelativeRegion ↔
      (coordinate + cell.1, cell.2) ∈ periodicStrip.carrier := by
  change
    (((periodicStrip.phaseAt wellFormed.2.1 coordinate).val : Int) +
        cell.1, cell.2) ∈ periodicStrip.carrier ↔
      (coordinate + cell.1, cell.2) ∈ periodicStrip.carrier
  apply periodicStrip.mem_carrier_congr_x
  rw [periodicStrip.phaseAt_val_int wellFormed.2.1]
  refine ⟨coordinate / periodicStrip.period, ?_⟩
  have division :=
    Int.emod_add_mul_ediv coordinate periodicStrip.period
  ring_nf at division ⊢
  omega

/-- A cell belongs to a placement exactly when its horizontal translate
belongs to the translated placement. -/
theorem mem_translatePlacement_cells_iff (tromino : Tromino)
    (coordinate : Int) (placement : Placement Unit) (cell : Cell) :
    (coordinate + cell.1, cell.2) ∈
        (translatePlacement coordinate placement).cells
          (fun _ : Unit => tromino.cells) ↔
      cell ∈ placement.cells (fun _ : Unit => tromino.cells) := by
  simp only [Placement.mem_cells_iff]
  constructor
  · rintro ⟨source, sourceMem, equality⟩
    refine ⟨source, sourceMem, ?_⟩
    apply Prod.ext
    · have xEquality := congrArg Prod.fst equality
      simp only [translatePlacement, Cell.add] at xEquality ⊢
      omega
    · have yEquality := congrArg Prod.snd equality
      simpa only [translatePlacement, Cell.add] using yEquality
  · rintro ⟨source, sourceMem, equality⟩
    refine ⟨source, sourceMem, ?_⟩
    apply Prod.ext
    · have xEquality := congrArg Prod.fst equality
      simp only [translatePlacement, Cell.add] at xEquality ⊢
      omega
    · have yEquality := congrArg Prod.snd equality
      simpa only [translatePlacement, Cell.add] using yEquality

/-- Every window cut from a globally locally valid assignment satisfies its
center-column tiling constraints. -/
theorem ofAssignment_isCenterValid (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    {assignment : TrominoAssignment}
    (valid :
      assignment.IsLocallyValid tromino periodicStrip.carrier)
    (coordinate : Int) :
    (ofAssignment wellFormed.2.1 assignment coordinate).IsCenterValid
      tromino := by
  constructor
  · intro base baseAtPhase symmetry selected cell cellMem
    have selectedGlobal :
        assignment (coordinate, base.val.2) = some symmetry := by
      change (if _ : base.val.1 =
          ((periodicStrip.phaseAt wellFormed.2.1
            (coordinate + center.displacement)).val : Int) then
        assignment (coordinate + center.displacement, base.val.2)
      else none) = some symmetry at selected
      have condition : base.val.1 =
          ((periodicStrip.phaseAt wellFormed.2.1
            (coordinate + center.displacement)).val : Int) := by
        simpa using baseAtPhase
      rw [dif_pos condition] at selected
      simpa using selected
    apply (ofAssignment_mem_relativeRegion_iff
      wellFormed assignment coordinate cell).mpr
    apply valid.1 (coordinate, base.val.2) symmetry selectedGlobal
    have translatedMem :=
      (mem_translatePlacement_cells_iff tromino coordinate
        (Placement.mk () symmetry (0, base.val.2)) cell).mpr cellMem
    simpa [translatePlacement] using translatedMem
  · intro base baseAtPhase
    rw [ofAssignment_activeCandidateCount
      tromino wellFormed valid coordinate base.val.2]
    apply valid.2
    apply (periodicStrip.mem_carrier_phaseAt_iff
      wellFormed.2.1 coordinate base.val.2).mpr
    apply (periodicStrip.mem_carrier_phase_iff_mem_motif
      wellFormed
      (periodicStrip.phaseAt wellFormed.2.1 coordinate)
      base.val.2).mpr
    have baseEq : base.val =
        (((periodicStrip.phaseAt wellFormed.2.1 coordinate).val : Int),
          base.val.2) := by
      apply Prod.ext
      · exact baseAtPhase
      · rfl
    rw [← baseEq]
    exact base.property

/-- A valid global assignment therefore gives one step of the sparse frontier
transition system at every integer coordinate. -/
theorem ofAssignment_transition (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    {assignment : TrominoAssignment}
    (valid :
      assignment.IsLocallyValid tromino periodicStrip.carrier)
    (coordinate : Int) :
    Transition tromino
      (ofAssignment wellFormed.2.1 assignment coordinate)
      (ofAssignment wellFormed.2.1 assignment (coordinate + 1)) :=
  ⟨ofAssignment_isNormalized _ _ _,
    ofAssignment_isCenterValid tromino wellFormed valid coordinate,
    ofAssignment_overlaps _ _ _⟩

/-- A valid global assignment yields a bi-infinite frontier path. -/
theorem hasBiInfinitePath_of_isLocallyValid (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    {assignment : TrominoAssignment}
    (valid :
      assignment.IsLocallyValid tromino periodicStrip.carrier) :
    FiniteState.HasBiInfinitePath
      (Transition tromino :
        WindowState periodicStrip → WindowState periodicStrip → Prop) :=
  ⟨fun coordinate =>
      ofAssignment wellFormed.2.1 assignment coordinate,
    ofAssignment_transition tromino wellFormed valid⟩

end LeanTrominoes.PeriodicStrip.WindowState
