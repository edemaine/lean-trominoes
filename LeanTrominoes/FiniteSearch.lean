/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TilingCompactness
import Mathlib.Data.Finset.Union

/-!
# Finite search for tromino box constraints

Each centered-box constraint system inspects only finitely many assignment
offsets: offsets in the box itself and offsets of placements that could cover
a target cell in the box. This file restricts assignments to exactly those
offsets and defines a decidable verifier.
-/

namespace LeanTrominoes
namespace TrominoAssignment

/-- The cells of the centered integer box as a finset. -/
def boxCells (radius : Nat) : Finset Cell :=
  (Finset.Icc (-(radius : Int)) (radius : Int)).product
    (Finset.Icc (-(radius : Int)) (radius : Int))

theorem mem_boxCells_iff (radius : Nat) (cell : Cell) :
    cell ∈ boxCells radius ↔ LeanWang.InBox radius cell := by
  simp [boxCells, LeanWang.InBox, and_assoc]

/-- Assignment offsets inspected by the radius-`radius` constraint system. -/
def inspectedOffsets (tromino : Tromino) (radius : Nat) : Finset Cell :=
  boxCells radius ∪
    (boxCells radius).biUnion fun cell =>
      (coveringPlacements tromino cell).image Placement.offset

theorem boxCell_mem_inspectedOffsets (tromino : Tromino) {radius : Nat}
    {cell : Cell} (cell_mem : cell ∈ boxCells radius) :
    cell ∈ inspectedOffsets tromino radius := by
  exact Finset.mem_union_left _ cell_mem

theorem candidateOffset_mem_inspectedOffsets (tromino : Tromino) {radius : Nat}
    {cell : Cell} (cell_mem : cell ∈ boxCells radius)
    {placement : Placement Unit}
    (placement_mem : placement ∈ coveringPlacements tromino cell) :
    placement.offset ∈ inspectedOffsets tromino radius := by
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨cell, cell_mem, Finset.mem_image.mpr ⟨placement, placement_mem, rfl⟩⟩

/-- A genuinely finite assignment containing every state inspected by one box
constraint system. -/
abbrev FiniteBoxAssignment (tromino : Tromino) (radius : Nat) :=
  ↑(inspectedOffsets tromino radius) → Option SquareSymmetry

/-- View a box cell as one of the inspected offsets. -/
def boxOffset (tromino : Tromino) {radius : Nat}
    (cell : ↑(boxCells radius)) : ↑(inspectedOffsets tromino radius) :=
  ⟨cell.val, boxCell_mem_inspectedOffsets tromino cell.property⟩

/-- View the offset of a candidate placement as one of the inspected offsets. -/
def candidateOffset (tromino : Tromino) {radius : Nat}
    (cell : ↑(boxCells radius))
    (placement : ↑(coveringPlacements tromino cell.val)) :
    ↑(inspectedOffsets tromino radius) :=
  ⟨placement.val.offset,
    candidateOffset_mem_inspectedOffsets tromino cell.property placement.property⟩

/-- Extend a finite box assignment to a global assignment, using `none` away
from the inspected offsets. -/
def FiniteBoxAssignment.extend {tromino : Tromino} {radius : Nat}
    (assignment : FiniteBoxAssignment tromino radius) : TrominoAssignment :=
  fun offset =>
    if offset_mem : offset ∈ inspectedOffsets tromino radius then
      assignment ⟨offset, offset_mem⟩
    else
      none

@[simp]
theorem FiniteBoxAssignment.extend_boxOffset {tromino : Tromino} {radius : Nat}
    (assignment : FiniteBoxAssignment tromino radius)
    (cell : ↑(boxCells radius)) :
    assignment.extend (boxOffset tromino cell) = assignment (boxOffset tromino cell) := by
  simp [FiniteBoxAssignment.extend]

@[simp]
theorem FiniteBoxAssignment.extend_candidateOffset {tromino : Tromino}
    {radius : Nat} (assignment : FiniteBoxAssignment tromino radius)
    (cell : ↑(boxCells radius))
    (placement : ↑(coveringPlacements tromino cell.val)) :
    assignment.extend placement.val.offset =
      assignment (candidateOffset tromino cell placement) := by
  unfold FiniteBoxAssignment.extend
  rw [dif_pos (candidateOffset_mem_inspectedOffsets tromino
    cell.property placement.property)]
  rfl

/-- Number of active candidates for a box cell in a finite assignment. -/
def finiteActiveCandidateCount {tromino : Tromino} {radius : Nat}
    (assignment : FiniteBoxAssignment tromino radius)
    (cell : ↑(boxCells radius)) : Nat :=
  ((coveringPlacements tromino cell.val).attach.filter fun placement =>
    assignment (candidateOffset tromino cell placement) =
      some placement.val.symmetry).card

theorem finiteActiveCandidateCount_eq_extend {tromino : Tromino} {radius : Nat}
    (assignment : FiniteBoxAssignment tromino radius)
    (cell : ↑(boxCells radius)) :
    finiteActiveCandidateCount assignment cell =
      ((coveringPlacements tromino cell.val).filter fun placement =>
        assignment.extend placement.offset = some placement.symmetry).card := by
  rw [← activeCandidateCount_observation tromino cell.val assignment.extend]
  unfold finiteActiveCandidateCount activeCandidateCount candidateObservation
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro placement placement_mem
  rw [FiniteBoxAssignment.extend_candidateOffset assignment cell placement]

/-- Decidable verifier for a finite box assignment. -/
def IsFiniteValid (tromino : Tromino) (region : Set Cell) (radius : Nat)
    (assignment : FiniteBoxAssignment tromino radius) : Prop :=
  (∀ offset : ↑(boxCells radius), ∀ symmetry,
      ∀ cell ∈ (Placement.mk () symmetry offset.val).cells
          (fun _ : Unit => tromino.cells),
        assignment (boxOffset tromino offset) = some symmetry → cell ∈ region) ∧
    ∀ cell : ↑(boxCells radius), cell.val ∈ region →
      finiteActiveCandidateCount assignment cell = 1

instance (tromino : Tromino) (region : Set Cell)
    [regionDecidable : DecidablePred region]
    (radius : Nat) (assignment : FiniteBoxAssignment tromino radius) :
    Decidable (IsFiniteValid tromino region radius assignment) := by
  unfold IsFiniteValid
  letI regionMembership (cell : Cell) : Decidable (cell ∈ region) :=
    regionDecidable cell
  exact instDecidableAnd

/-- The finite verifier agrees with box validity for the extended global
assignment. -/
theorem isFiniteValid_iff_extend_isValidInBox (tromino : Tromino)
    (region : Set Cell) (radius : Nat)
    (assignment : FiniteBoxAssignment tromino radius) :
    IsFiniteValid tromino region radius assignment ↔
      assignment.extend.IsValidInBox tromino region radius := by
  constructor
  · rintro ⟨inside, covered⟩
    constructor
    · intro offset offset_in symmetry cell cell_mem selected
      let boxedOffset : ↑(boxCells radius) :=
        ⟨offset, (mem_boxCells_iff radius offset).mpr offset_in⟩
      apply inside boxedOffset symmetry cell cell_mem
      change assignment.extend (boxOffset tromino boxedOffset) = some symmetry at selected
      rw [FiniteBoxAssignment.extend_boxOffset] at selected
      exact selected
    · intro cell cell_in cell_mem
      let boxedCell : ↑(boxCells radius) :=
        ⟨cell, (mem_boxCells_iff radius cell).mpr cell_in⟩
      rw [← finiteActiveCandidateCount_eq_extend assignment boxedCell]
      exact covered boxedCell cell_mem
  · rintro ⟨inside, covered⟩
    constructor
    · intro offset symmetry cell cell_mem selected
      apply inside offset.val ((mem_boxCells_iff radius offset.val).mp offset.property)
        symmetry cell cell_mem
      change assignment.extend (boxOffset tromino offset) = some symmetry
      rw [FiniteBoxAssignment.extend_boxOffset]
      exact selected
    · intro cell cell_mem
      rw [finiteActiveCandidateCount_eq_extend]
      exact covered cell.val ((mem_boxCells_iff radius cell.val).mp cell.property) cell_mem

/-- Restrict a global assignment to the offsets inspected by a finite box. -/
def FiniteBoxAssignment.restrict {tromino : Tromino} {radius : Nat}
    (assignment : TrominoAssignment) : FiniteBoxAssignment tromino radius :=
  fun offset => assignment offset.val

/-- A globally valid box restricts to an accepted finite assignment. -/
theorem isFiniteValid_restrict_of_isValidInBox (tromino : Tromino)
    (region : Set Cell) (radius : Nat) (assignment : TrominoAssignment)
    (valid : assignment.IsValidInBox tromino region radius) :
    IsFiniteValid tromino region radius
      (FiniteBoxAssignment.restrict assignment) := by
  constructor
  · intro offset symmetry cell cell_mem selected
    exact valid.1 offset.val ((mem_boxCells_iff radius offset.val).mp offset.property)
      symmetry cell cell_mem selected
  · intro cell cell_mem
    have globally_covered :=
      valid.2 cell.val ((mem_boxCells_iff radius cell.val).mp cell.property) cell_mem
    rw [← activeCandidateCount_observation tromino cell.val assignment] at globally_covered
    exact globally_covered

/-- Satisfiability of the decidable finite constraint system. -/
def IsBoxSatisfiable (tromino : Tromino) (region : Set Cell) (radius : Nat) : Prop :=
  ∃ assignment : FiniteBoxAssignment tromino radius,
    IsFiniteValid tromino region radius assignment

instance (tromino : Tromino) (region : Set Cell) [DecidablePred region]
    (radius : Nat) : Decidable (IsBoxSatisfiable tromino region radius) :=
  Fintype.decidableExistsFintype

theorem isBoxSatisfiable_iff_exists_isValidInBox (tromino : Tromino)
    (region : Set Cell) (radius : Nat) :
    IsBoxSatisfiable tromino region radius ↔
      ∃ assignment : TrominoAssignment,
        assignment.IsValidInBox tromino region radius := by
  constructor
  · rintro ⟨assignment, valid⟩
    exact ⟨assignment.extend,
      (isFiniteValid_iff_extend_isValidInBox tromino region radius assignment).mp valid⟩
  · rintro ⟨assignment, valid⟩
    exact ⟨FiniteBoxAssignment.restrict assignment,
      isFiniteValid_restrict_of_isValidInBox tromino region radius assignment valid⟩

/-- Final finite-obstruction characterization: a region is tileable exactly
when every finite box constraint system is satisfiable. -/
theorem tileable_iff_forall_isBoxSatisfiable (tromino : Tromino)
    (region : Set Cell) :
    tromino.Tileable region ↔
      ∀ radius : Nat, IsBoxSatisfiable tromino region radius := by
  rw [tileable_iff_forall_exists_isValidInBox]
  constructor
  · intro valid radius
    exact (isBoxSatisfiable_iff_exists_isValidInBox
      tromino region radius).mpr (valid radius)
  · intro valid radius
    exact (isBoxSatisfiable_iff_exists_isValidInBox
      tromino region radius).mp (valid radius)

end TrominoAssignment
end LeanTrominoes
