/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetIPhaseLift

/-! # Canonical I-gadget states depend only on active inward bits

Selecting the same finite pattern for the same active profile lets finite
prescriptions coexist with the global preferred-phase construction.
-/
noncomputable section
namespace LeanTrominoes.Gadget.PreferredISelection

def profile (kind : OrthogonalCellType) (inward : Side → Bool) : Side → Bool :=
  fun side => if (kind.portColor side).isSome then inward side else false

def Witness (kind : OrthogonalCellType) (inward : Side → Bool)
    (pattern : Finset (Placement Unit)) : Prop :=
  pattern ∈ exactCellTilings .I kind ∧
  (kind,portConfiguration .I (orthogonalCellGadget .I kind) pattern) ∈ iPreferredCellPortTable ∧
  IEntryRealizes (kind,portConfiguration .I (orthogonalCellGadget .I kind) pattern) inward

private def selectPattern (kind : OrthogonalCellType) (inward : Side → Bool) : Finset (Placement Unit) := by
  classical
  exact if h : ∃ placements, Witness kind inward placements then Classical.choose h else ∅

def pattern (kind : OrthogonalCellType) (inward : Side → Bool) : Finset (Placement Unit) :=
  selectPattern kind (profile kind inward)

theorem exists_witness (kind : OrthogonalCellType) (inward : Side → Bool)
    (valid : PeriodicOrthogonalDrawing.satisfiesOrientation kind inward) :
    ∃ placements, Witness kind (profile kind inward) placements := by
  obtain ⟨entry,typeEqual,realizes⟩ := iPreferredPhaseTableCorrect.1 kind inward valid
  have separated : entry.1 ∈ iSeparatedCellPortTable :=
    (Finset.mem_filter.mp entry.property).1
  obtain ⟨placements,exact,ports⟩ := exists_exactCellTiling_of_mem_iSeparated
    entry.1.1 entry.1.2 separated
  have pairEqual : (kind,portConfiguration .I (orthogonalCellGadget .I kind) placements) = entry.1 := by
    cases typeEqual
    exact Prod.ext rfl ports
  refine ⟨placements,?_,pairEqual.symm ▸ entry.property,?_⟩
  · simpa only [typeEqual] using exact
  · intro side active
    rw [pairEqual]
    rw [typeEqual]
    simpa only [profile,if_pos active] using realizes side active

theorem pattern_spec (kind : OrthogonalCellType) (inward : Side → Bool)
    (valid : PeriodicOrthogonalDrawing.satisfiesOrientation kind inward) :
    Witness kind (profile kind inward) (pattern kind inward) := by
  unfold pattern selectPattern
  rw [dif_pos (exists_witness kind inward valid)]
  exact Classical.choose_spec (exists_witness kind inward valid)

theorem pattern_eq_of_active_eq (kind : OrthogonalCellType) (a b : Side → Bool)
    (same : ∀ side, (kind.portColor side).isSome → a side = b side) :
    pattern kind a = pattern kind b := by
  have equal : profile kind a = profile kind b := by
    funext side
    unfold profile
    split
    · exact same side ‹_›
    · rfl
  unfold pattern
  rw [equal]

def assignment (drawing : PeriodicOrthogonalDrawing) (inward : drawing.Orientation) :
    LocalTilingAssignment .I drawing := fun cell => pattern (drawing.getAt cell) (inward cell)

theorem assignment_locallyTiled (drawing : PeriodicOrthogonalDrawing)
    (inward : drawing.Orientation) (valid : drawing.IsOrientation inward) :
    IsLocallyTiled .I drawing (assignment drawing inward) :=
  fun cell => (pattern_spec _ _ (valid.1 cell)).1

theorem assignment_realizes (drawing : PeriodicOrthogonalDrawing)
    (inward : drawing.Orientation) (valid : drawing.IsOrientation inward)
    (cell : Cell) (side : Side) (active : ((drawing.getAt cell).portColor side).isSome) :
    iConfigurationInward (drawing.getAt cell)
      (selectedPortConfiguration .I drawing (assignment drawing inward) cell) side = inward cell side := by
  have realized := (pattern_spec _ _ (valid.1 cell)).2.2 side active
  simpa only [selectedPortConfiguration,assignment,profile,if_pos active] using realized

theorem assignment_ports (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed)
    (inward : drawing.Orientation) (valid : drawing.IsOrientation inward) (cell : Cell) (side : Side) :
    (selectedPortConfiguration .I drawing (assignment drawing inward) cell).get side =
      (selectedPortConfiguration .I drawing (assignment drawing inward)
        (PeriodicOrthogonalDrawing.latticeNeighbor cell side)).get side.opposite := by
  let neighbor := PeriodicOrthogonalDrawing.latticeNeighbor cell side
  let left : IPreferredEntry := ⟨_,(pattern_spec _ _ (valid.1 cell)).2.1⟩
  let right : IPreferredEntry := ⟨_,(pattern_spec _ _ (valid.1 neighbor)).2.1⟩
  change left.1.2.get side = right.1.2.get side.opposite
  have colors := drawing.portColor_latticeNeighbor_eq wf cell side
  cases colorMatch : (drawing.getAt cell).portColor side with
  | some color =>
    rw [colorMatch] at colors
    have active : ((drawing.getAt cell).portColor side).isSome := by simp [colorMatch]
    have neighborActive : ((drawing.getAt neighbor).portColor side.opposite).isSome := by
      change ((drawing.getAt (PeriodicOrthogonalDrawing.latticeNeighbor cell side)).portColor side.opposite).isSome
      rw [← colors]
      rfl
    apply iPreferredPhaseTableCorrect.2 left right side color colorMatch colors.symm
    change iConfigurationInward _ (selectedPortConfiguration .I drawing (assignment drawing inward) cell) side =
      !(iConfigurationInward _ (selectedPortConfiguration .I drawing (assignment drawing inward) neighbor) side.opposite)
    rw [assignment_realizes drawing inward valid cell side active,
      assignment_realizes drawing inward valid neighbor side.opposite neighborActive]
    exact valid.2 cell side active
  | none =>
    rw [colorMatch] at colors
    have leftSeparated := (Finset.mem_filter.mp left.property).1
    have rightSeparated := (Finset.mem_filter.mp right.property).1
    rw [iLocalOrientationTableCorrect.2.2.1 ⟨left.1,leftSeparated⟩ side colorMatch,
      iLocalOrientationTableCorrect.2.2.1 ⟨right.1,rightSeparated⟩ side.opposite colors.symm]

theorem assignment_compatible (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed)
    (inward : drawing.Orientation) (valid : drawing.IsOrientation inward) :
    IsPortCompatible .I drawing (assignment drawing inward) :=
  ⟨fun cell => assignment_ports drawing wf inward valid cell .east,
    fun cell => assignment_ports drawing wf inward valid cell .south⟩

end LeanTrominoes.Gadget.PreferredISelection
