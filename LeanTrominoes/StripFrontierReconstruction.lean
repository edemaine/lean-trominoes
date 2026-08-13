/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateCycleSearch
import LeanTrominoes.StripFrontierCorrectness

/-!
# Reconstruction from sparse periodic strip frontiers

This file proves the converse to frontier extraction.  It aligns the cyclic
phase of an arbitrary bi-infinite frontier path with actual strip coordinates,
uses four-column overlap to reconstruct one global assignment, and verifies
all local tiling constraints.  Combined with finite-state pumping, it
characterizes periodic strip tileability by a finite directed cycle.
-/

namespace LeanTrominoes.PeriodicStrip.WindowState

theorem path_phase {periodicStrip : PeriodicStrip}
    {tromino : Tromino} {path : Int → WindowState periodicStrip}
    (step : FiniteState.IsBiInfinitePath (Transition tromino) path)
    (index : Int) :
    (path index).phase = shiftPhase (path 0).phase index := by
  induction index using Int.induction_on with
  | zero => simp
  | succ index ih =>
      calc
        (path (index + 1)).phase =
            shiftPhase (path index).phase 1 := (step index).2.2.1
        _ = shiftPhase (shiftPhase (path 0).phase index) 1 := by rw [ih]
        _ = shiftPhase (path 0).phase (index + 1) := by
          rw [shiftPhase_add]
  | pred index ih =>
      have previous :=
        (step (-(index : Int) - 1)).2.2.1
      have phasePrevious :
          (path (-(index : Int) - 1)).phase =
            shiftPhase (path (-(index : Int))).phase (-1) := by
        apply_fun fun phase => shiftPhase phase (-1) at previous
        simpa [shiftPhase_add] using previous.symm
      calc
        (path (-↑index - 1)).phase =
            shiftPhase (path (-↑index)).phase (-1) := phasePrevious
        _ = shiftPhase (shiftPhase (path 0).phase (-↑index)) (-1) := by
          rw [ih]
        _ = shiftPhase (path 0).phase (-↑index - 1) := by
          rw [shiftPhase_add]
          congr 1

/-- Shifting a phase by the difference from its numeric representative aligns
it with the canonical phase of the requested coordinate. -/
theorem shiftPhase_sub_val_eq_phaseAt (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (phase : Fin periodicStrip.period) (coordinate : Int) :
    shiftPhase phase (coordinate - phase.val) =
      periodicStrip.phaseAt periodPositive coordinate := by
  apply Fin.ext
  simp only [shiftPhase, phaseAt]
  congr 1
  ring_nf

/-- Reindex a frontier path so its state phase agrees with each actual
horizontal coordinate. -/
def alignedState {periodicStrip : PeriodicStrip}
    (path : Int → WindowState periodicStrip) (coordinate : Int) :
    WindowState periodicStrip :=
  path (coordinate - (path 0).phase.val)

theorem alignedState_phase {periodicStrip : PeriodicStrip}
    {tromino : Tromino} {path : Int → WindowState periodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    (step : FiniteState.IsBiInfinitePath (Transition tromino) path)
    (coordinate : Int) :
    (alignedState path coordinate).phase =
      periodicStrip.phaseAt wellFormed.2.1 coordinate := by
  rw [alignedState, path_phase step]
  exact shiftPhase_sub_val_eq_phaseAt periodicStrip wellFormed.2.1
    (path 0).phase coordinate

/-- Overlapping windows give identical row values in every shared column. -/
theorem valueAt_overlap {periodicStrip : PeriodicStrip}
    (current next : WindowState periodicStrip)
    (overlaps : current.Overlaps next)
    (column : Fin 4) (row : Int) :
    current.valueAt column.succ row =
      next.valueAt column.castSucc row := by
  have phaseEq := columnPhase_overlap current next overlaps column
  unfold valueAt
  rw [phaseEq]
  let cell : Cell := ((next.columnPhase column.castSucc).val, row)
  change (if cellMem : cell ∈ periodicStrip.motif.toFinset then
      current.assignment column.succ ⟨cell, cellMem⟩ else none) =
    if cellMem : cell ∈ periodicStrip.motif.toFinset then
      next.assignment column.castSucc ⟨cell, cellMem⟩ else none
  by_cases cellMem : cell ∈ periodicStrip.motif.toFinset
  · rw [dif_pos cellMem, dif_pos cellMem]
    apply overlaps.2
  · rw [dif_neg cellMem, dif_neg cellMem]

/-- Every column value along a frontier path equals the center value at the
correspondingly shifted path index. -/
theorem valueAt_eq_path_center {periodicStrip : PeriodicStrip}
    {tromino : Tromino} {path : Int → WindowState periodicStrip}
    (step : FiniteState.IsBiInfinitePath (Transition tromino) path)
    (index : Int) (column : WindowColumn) (row : Int) :
    (path index).valueAt column row =
      (path (index + column.displacement)).valueAt center row := by
  have overlapAt (position : Int) :
      (path position).Overlaps (path (position + 1)) :=
    (step position).2.2
  fin_cases column
  · convert (calc
      (path index).valueAt (0 : WindowColumn) row =
          (path (index - 1)).valueAt (1 : WindowColumn) row := by
            symm
            simpa [center] using
              valueAt_overlap _ _ (overlapAt (index - 1))
                (0 : Fin 4) row
      _ = (path (index - 2)).valueAt center row := by
            symm
            convert valueAt_overlap _ _ (overlapAt (index - 2))
              (1 : Fin 4) row using 1
            all_goals simp [center]
            all_goals ring_nf) using 1
    all_goals simp [WindowColumn.displacement, center]
    all_goals ring_nf
  · convert (valueAt_overlap _ _ (overlapAt (index - 1))
      (1 : Fin 4) row).symm using 1
    all_goals simp [WindowColumn.displacement, center]
    all_goals ring_nf
  · simp [WindowColumn.displacement, center]
  · convert valueAt_overlap _ _ (overlapAt index)
      (2 : Fin 4) row using 1
    all_goals simp [WindowColumn.displacement, center]
  · convert (calc
      (path index).valueAt (4 : WindowColumn) row =
          (path (index + 1)).valueAt (3 : WindowColumn) row := by
            simpa [center] using
              valueAt_overlap _ _ (overlapAt index) (3 : Fin 4) row
      _ = (path (index + 2)).valueAt center row := by
            convert valueAt_overlap _ _ (overlapAt (index + 1))
              (2 : Fin 4) row using 1
            all_goals simp [center]
            all_goals ring_nf) using 1
    all_goals simp [WindowColumn.displacement, center]

/-- Every column value in an aligned window equals the center value of the
window aligned with that column's actual coordinate. -/
theorem valueAt_eq_aligned_center {periodicStrip : PeriodicStrip}
    {tromino : Tromino} {path : Int → WindowState periodicStrip}
    (step : FiniteState.IsBiInfinitePath (Transition tromino) path)
    (coordinate : Int) (column : WindowColumn) (row : Int) :
    (alignedState path coordinate).valueAt column row =
      (alignedState path (coordinate + column.displacement)).valueAt
        center row := by
  unfold alignedState
  convert valueAt_eq_path_center step
    (coordinate - (path 0).phase.val) column row using 1
  ring_nf

/-- Global assignment reconstructed from the aligned center values of a
bi-infinite frontier path. -/
def assignmentOfPath {periodicStrip : PeriodicStrip}
    (path : Int → WindowState periodicStrip) : TrominoAssignment :=
  fun offset => (alignedState path offset.1).valueAt center offset.2

/-- The local assignment carried by an aligned window agrees with the
reconstructed global assignment throughout that five-column window. -/
theorem localAssignment_eq_assignmentOfPath
    {periodicStrip : PeriodicStrip}
    {tromino : Tromino} {path : Int → WindowState periodicStrip}
    (step : FiniteState.IsBiInfinitePath (Transition tromino) path)
    (coordinate displacement row : Int)
    (lower : -2 ≤ displacement) (upper : displacement ≤ 2) :
    (alignedState path coordinate).localAssignment (displacement, row) =
      assignmentOfPath path (coordinate + displacement, row) := by
  obtain ⟨column, columnDisplacement⟩ :=
    exists_windowColumn_of_bounds lower upper
  subst displacement
  rw [localAssignment,
    WindowColumn.ofDisplacement?_displacement]
  exact valueAt_eq_aligned_center step coordinate column row

/-- Every aligned state on a valid transition path satisfies its center
constraints. -/
theorem alignedState_isCenterValid {periodicStrip : PeriodicStrip}
    {tromino : Tromino} {path : Int → WindowState periodicStrip}
    (step : FiniteState.IsBiInfinitePath (Transition tromino) path)
    (coordinate : Int) :
    (alignedState path coordinate).IsCenterValid tromino :=
  (step (coordinate - (path 0).phase.val)).2.1

/-- Relative membership in an aligned state is global carrier membership
after translating by its actual coordinate. -/
theorem alignedState_mem_relativeRegion_iff
    {periodicStrip : PeriodicStrip}
    {tromino : Tromino} {path : Int → WindowState periodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    (step : FiniteState.IsBiInfinitePath (Transition tromino) path)
    (coordinate : Int) (cell : Cell) :
    cell ∈ (alignedState path coordinate).RelativeRegion ↔
      (coordinate + cell.1, cell.2) ∈ periodicStrip.carrier := by
  change
    (((alignedState path coordinate).phase.val : Int) + cell.1,
        cell.2) ∈ periodicStrip.carrier ↔
      (coordinate + cell.1, cell.2) ∈ periodicStrip.carrier
  rw [alignedState_phase wellFormed step]
  apply periodicStrip.mem_carrier_congr_x
  rw [periodicStrip.phaseAt_val_int wellFormed.2.1]
  refine ⟨coordinate / periodicStrip.period, ?_⟩
  have division :=
    Int.emod_add_mul_ediv coordinate periodicStrip.period
  ring_nf at division ⊢
  omega

/-- Reconstructing an assignment from a path preserves the active-candidate
count between a local center cell and its global translate. -/
theorem assignmentOfPath_activeCandidateCount
    (tromino : Tromino) {periodicStrip : PeriodicStrip}
    {path : Int → WindowState periodicStrip}
    (step : FiniteState.IsBiInfinitePath (Transition tromino) path)
    (coordinate row : Int) :
    ((TrominoAssignment.coveringPlacements tromino (0, row)).filter
        fun placement =>
          (alignedState path coordinate).localAssignment placement.offset =
            some placement.symmetry).card =
      ((TrominoAssignment.coveringPlacements
          tromino (coordinate, row)).filter fun placement =>
        assignmentOfPath path placement.offset =
          some placement.symmetry).card := by
  let localActive :=
    (TrominoAssignment.coveringPlacements tromino (0, row)).filter
      fun placement =>
        (alignedState path coordinate).localAssignment placement.offset =
          some placement.symmetry
  let globalActive :=
    (TrominoAssignment.coveringPlacements
      tromino (coordinate, row)).filter fun placement =>
        assignmentOfPath path placement.offset =
          some placement.symmetry
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
      rw [localAssignment_eq_assignmentOfPath step coordinate
        localPlacement.offset.1 localPlacement.offset.2
          (by omega) (by omega)]
      change assignmentOfPath path
          (translatePlacement coordinate localPlacement).offset =
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
      change assignmentOfPath path
        (coordinate + localPlacement.offset.1, localPlacement.offset.2) =
          some localPlacement.symmetry
      rw [← localAssignment_eq_assignmentOfPath step coordinate
        localPlacement.offset.1 localPlacement.offset.2
          (by omega) (by omega)]
      simpa using localData.2
  change localActive.card = globalActive.card
  rw [activeEq, Finset.card_image_of_injective]
  intro first second equality
  have inverseEquality :=
    congrArg (translatePlacement (-coordinate)) equality
  simpa using inverseEquality

/-- A bi-infinite path of valid sparse frontier transitions reconstructs a
globally locally valid strip assignment. -/
theorem assignmentOfPath_isLocallyValid (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    {path : Int → WindowState periodicStrip}
    (step : FiniteState.IsBiInfinitePath (Transition tromino) path) :
    (assignmentOfPath path).IsLocallyValid
      tromino periodicStrip.carrier := by
  constructor
  · intro offset symmetry selected cell cellMem
    let state := alignedState path offset.1
    have centerValid : state.IsCenterValid tromino :=
      alignedState_isCenterValid step offset.1
    change state.valueAt center offset.2 = some symmetry at selected
    rw [valueAt, columnPhase_center] at selected
    let representative : Cell :=
      (((state.phase.val : Int), offset.2) : Cell)
    change (if representativeMem :
        representative ∈ periodicStrip.motif.toFinset then
      state.assignment center ⟨representative, representativeMem⟩
    else none) = some symmetry at selected
    by_cases representativeMem :
        representative ∈ periodicStrip.motif.toFinset
    · rw [dif_pos representativeMem] at selected
      let base : periodicStrip.MotifCell :=
        ⟨representative, representativeMem⟩
      let localCell : Cell := (cell.1 - offset.1, cell.2)
      have localCellMem :
          localCell ∈
            (Placement.mk () symmetry (0, offset.2)).cells
              (fun _ : Unit => tromino.cells) := by
        apply (mem_translatePlacement_cells_iff tromino offset.1
          (Placement.mk () symmetry (0, offset.2)) localCell).mp
        simpa [localCell, translatePlacement] using cellMem
      have relativeMem : localCell ∈ state.RelativeRegion := by
        apply centerValid.1 base
        · rfl
        · exact selected
        · exact localCellMem
      have translatedMem :=
        (alignedState_mem_relativeRegion_iff
          wellFormed step offset.1 localCell).mp relativeMem
      simpa [localCell] using translatedMem
    · rw [dif_neg representativeMem] at selected
      cases selected
  · intro cell cellMem
    let state := alignedState path cell.1
    have phaseEq :
        state.phase =
          periodicStrip.phaseAt wellFormed.2.1 cell.1 :=
      alignedState_phase wellFormed step cell.1
    have representativeCarrier :
        (((state.phase.val : Int), cell.2) : Cell) ∈
          periodicStrip.carrier := by
      rw [phaseEq]
      exact (periodicStrip.mem_carrier_phaseAt_iff
        wellFormed.2.1 cell.1 cell.2).mp cellMem
    have representativeMotif :
        (((state.phase.val : Int), cell.2) : Cell) ∈
          periodicStrip.motif.toFinset :=
      (periodicStrip.mem_carrier_phase_iff_mem_motif
        wellFormed state.phase cell.2).mp representativeCarrier
    let base : periodicStrip.MotifCell :=
      ⟨((state.phase.val : Int), cell.2), representativeMotif⟩
    have localCount :=
      (alignedState_isCenterValid step cell.1).2 base (by rfl)
    rw [assignmentOfPath_activeCandidateCount
      tromino step cell.1 cell.2] at localCount
    exact localCount

/-- Existence of a bi-infinite frontier path implies strip tileability. -/
theorem tileable_of_hasBiInfinitePath (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed)
    (infinite : FiniteState.HasBiInfinitePath
      (Transition tromino :
        WindowState periodicStrip → WindowState periodicStrip → Prop)) :
    tromino.Tileable periodicStrip.carrier := by
  obtain ⟨path, step⟩ := infinite
  apply (TrominoAssignment.exists_assignment_iff_tileable
    tromino periodicStrip.carrier).mp
  refine ⟨assignmentOfPath path, ?_⟩
  exact (TrominoAssignment.isLocallyValid_iff_isTiling
    tromino periodicStrip.carrier (assignmentOfPath path)).mp
      (assignmentOfPath_isLocallyValid tromino wellFormed step)

/-- For a well-formed strip, global tileability is exactly existence of a
bi-infinite path through the sparse frontier transition system. -/
theorem tileable_iff_hasBiInfinitePath (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed) :
    tromino.Tileable periodicStrip.carrier ↔
      FiniteState.HasBiInfinitePath
        (Transition tromino :
          WindowState periodicStrip → WindowState periodicStrip → Prop) := by
  constructor
  · intro tileable
    obtain ⟨assignment, tiling⟩ :=
      (TrominoAssignment.exists_assignment_iff_tileable
        tromino periodicStrip.carrier).mpr tileable
    have valid :=
      (TrominoAssignment.isLocallyValid_iff_isTiling
        tromino periodicStrip.carrier assignment).mpr tiling
    exact hasBiInfinitePath_of_isLocallyValid
      tromino wellFormed valid
  · exact tileable_of_hasBiInfinitePath tromino wellFormed

/-- Finite-state pumping turns the frontier-path characterization into an
equivalent finite directed-cycle certificate. -/
theorem tileable_iff_hasCycle (tromino : Tromino)
    {periodicStrip : PeriodicStrip}
    (wellFormed : periodicStrip.IsWellFormed) :
    tromino.Tileable periodicStrip.carrier ↔
      FiniteState.HasCycle
        (Transition tromino :
          WindowState periodicStrip → WindowState periodicStrip → Prop) := by
  rw [tileable_iff_hasBiInfinitePath tromino wellFormed,
    FiniteState.hasBiInfinitePath_iff_hasCycle]

/-- The complete 1.5D tiling predicate, including malformed-input rejection,
has a finite directed-cycle characterization. -/
theorem periodicStripTrominoTiling_iff_hasCycle
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    PeriodicStripTrominoTiling tromino periodicStrip ↔
      periodicStrip.IsWellFormed ∧
        FiniteState.HasCycle
          (Transition tromino :
            WindowState periodicStrip → WindowState periodicStrip → Prop) := by
  unfold PeriodicStripTrominoTiling
  constructor
  · rintro ⟨wellFormed, tileable⟩
    exact ⟨wellFormed,
      (tileable_iff_hasCycle tromino wellFormed).mp tileable⟩
  · rintro ⟨wellFormed, cycle⟩
    exact ⟨wellFormed,
      (tileable_iff_hasCycle tromino wellFormed).mpr cycle⟩

/-- Equivalently, a certificate never needs more states than the finite
frontier graph itself contains. -/
theorem periodicStripTrominoTiling_iff_hasBoundedCycle
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    PeriodicStripTrominoTiling tromino periodicStrip ↔
      periodicStrip.IsWellFormed ∧
        FiniteState.HasBoundedCycle
          (Transition tromino :
            WindowState periodicStrip → WindowState periodicStrip → Prop) := by
  rw [periodicStripTrominoTiling_iff_hasCycle,
    FiniteState.hasCycle_iff_hasBoundedCycle]

/-- Executable sparse-frontier decision procedure for periodic strip
tromino tiling.  Its cycle test uses logarithmic-depth reachability rather
than storing an entire cycle certificate. -/
def periodicStripTrominoTilingBool
    (tromino : Tromino) (periodicStrip : PeriodicStrip) : Bool :=
  periodicStrip.wellFormed &&
    FiniteState.cycleSearchBool
      (Transition tromino :
        WindowState periodicStrip → WindowState periodicStrip → Prop)

theorem periodicStripTrominoTilingBool_eq_true_iff
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    periodicStripTrominoTilingBool tromino periodicStrip = true ↔
      PeriodicStripTrominoTiling tromino periodicStrip := by
  rw [periodicStripTrominoTilingBool, Bool.and_eq_true,
    periodicStrip.wellFormed_eq_true_iff,
    FiniteState.cycleSearchBool_eq_true_iff,
    periodicStripTrominoTiling_iff_hasCycle]

/-- Periodic strip tromino tiling is decidable by the verified
logarithmic-depth sparse-frontier cycle search.  The stronger
polynomial-space machine bound is proved separately. -/
instance periodicStripTrominoTilingDecidable
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    Decidable (PeriodicStripTrominoTiling tromino periodicStrip) :=
  decidable_of_iff
    (periodicStripTrominoTilingBool tromino periodicStrip = true)
    (periodicStripTrominoTilingBool_eq_true_iff
      tromino periodicStrip)

end LeanTrominoes.PeriodicStrip.WindowState
