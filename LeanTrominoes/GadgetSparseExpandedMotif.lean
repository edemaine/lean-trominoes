/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetReductionComputability
import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentLookup

/-! # Sparse gadget motifs from collision-free cell assignments -/

namespace LeanTrominoes
namespace Gadget

/-- Origin of a gadget block whose drawing-cell location is stored with
integer coordinates. -/
def sparseBlockOrigin (location : Cell) : Cell :=
  Cell.scale 6 location

/-- Gadget pixels contributed by one explicitly listed drawing-cell
assignment. -/
def sparseAssignmentPixels (tromino : Tromino)
    (assignment : Cell × OrthogonalCellType) : List Cell :=
  (orthogonalCellPixels tromino assignment.2).map fun pixel =>
    Cell.add (sparseBlockOrigin assignment.1) pixel

/-- Concatenate the gadget pixels of a sparse drawing-cell assignment list. -/
def sparseExpandedMotif (tromino : Tromino)
    (assignments : List (Cell × OrthogonalCellType)) : List Cell :=
  assignments.flatMap (sparseAssignmentPixels tromino)

theorem sparseBlockOrigin_nat (horizontal vertical : Nat) :
    sparseBlockOrigin ((horizontal : Int), (vertical : Int)) =
      PeriodicOrthogonalDrawing.blockOrigin horizontal vertical := by
  simp [sparseBlockOrigin, PeriodicOrthogonalDrawing.blockOrigin,
    Cell.scale]

/-- Natural-index lookup agrees definitionally with dependent finite-index
lookup inside the drawing domain. -/
@[simp] theorem PeriodicOrthogonalDrawing.indexedCellType_eq_get
    (drawing : PeriodicOrthogonalDrawing)
    (horizontal : Fin drawing.horizontalPeriod)
    (vertical : Fin drawing.verticalPeriod) :
    drawing.indexedCellType horizontal.val vertical.val =
      drawing.get (horizontal, vertical) :=
  rfl

/-- A collision-free sparse assignment list whose lookup is the drawing's
finite cell lookup contributes exactly the same motif cells as the full
natural-range raster. -/
theorem mem_sparseExpandedMotif_iff
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (assignments : List (Cell × OrthogonalCellType))
    (keysNodup : (assignments.map Prod.fst).Nodup)
    (bounds : ∀ assignment ∈ assignments,
      0 ≤ assignment.1.1 ∧
        assignment.1.1 < (drawing.horizontalPeriod : Int) ∧
        0 ≤ assignment.1.2 ∧
        assignment.1.2 < (drawing.verticalPeriod : Int))
    (lookupRepresents : ∀ horizontal vertical,
      horizontal < drawing.horizontalPeriod →
      vertical < drawing.verticalPeriod →
      drawing.indexedCellType horizontal vertical =
        (assignments.lookup
          (((horizontal : Int), (vertical : Int)) : Cell)).getD .blank)
    (cell : Cell) :
    cell ∈ sparseExpandedMotif tromino assignments ↔
      cell ∈ drawing.computableExpandedMotif tromino := by
  constructor
  · intro member
    simp only [sparseExpandedMotif, List.mem_flatMap] at member
    obtain ⟨assignment, assignmentMember, pixelMember⟩ := member
    simp only [sparseAssignmentPixels, List.mem_map] at pixelMember
    obtain ⟨pixel, pixelTypeMember, rfl⟩ := pixelMember
    have assignmentBounds := bounds assignment assignmentMember
    let horizontal := assignment.1.1.toNat
    let vertical := assignment.1.2.toNat
    have horizontalCast : (horizontal : Int) = assignment.1.1 := by
      exact Int.toNat_of_nonneg assignmentBounds.1
    have verticalCast : (vertical : Int) = assignment.1.2 := by
      exact Int.toNat_of_nonneg assignmentBounds.2.2.1
    have horizontalBound : horizontal < drawing.horizontalPeriod := by
      rw [Int.toNat_lt assignmentBounds.1]
      exact assignmentBounds.2.1
    have verticalBound : vertical < drawing.verticalPeriod := by
      rw [Int.toNat_lt assignmentBounds.2.2.1]
      exact assignmentBounds.2.2.2
    have keyEquality :
        (((horizontal : Int), (vertical : Int)) : Cell) = assignment.1 := by
      apply Prod.ext
      · exact horizontalCast
      · exact verticalCast
    have assignmentLookup :
        assignments.lookup assignment.1 = some assignment.2 :=
      PeriodicThreeDM.List.lookup_eq_some_of_mem_of_nodup_keys
        assignmentMember keysNodup
    have cellTypeEquality :
        drawing.indexedCellType horizontal vertical = assignment.2 := by
      rw [lookupRepresents horizontal vertical horizontalBound verticalBound,
        keyEquality, assignmentLookup]
      rfl
    simp only [PeriodicOrthogonalDrawing.computableExpandedMotif,
      List.mem_flatMap]
    refine ⟨horizontal, List.mem_range.mpr horizontalBound,
      vertical, List.mem_range.mpr verticalBound, ?_⟩
    simp only [PeriodicOrthogonalDrawing.indexedExpandedBlockPixels,
      List.mem_map]
    refine ⟨pixel, ?_, ?_⟩
    · rwa [cellTypeEquality]
    · rw [← sparseBlockOrigin_nat horizontal vertical, keyEquality]
  · intro member
    simp only [PeriodicOrthogonalDrawing.computableExpandedMotif,
      List.mem_flatMap] at member
    obtain ⟨horizontal, horizontalMember, vertical, verticalMember,
      pixelMember⟩ := member
    have horizontalBound := List.mem_range.mp horizontalMember
    have verticalBound := List.mem_range.mp verticalMember
    simp only [PeriodicOrthogonalDrawing.indexedExpandedBlockPixels,
      List.mem_map] at pixelMember
    obtain ⟨pixel, pixelTypeMember, rfl⟩ := pixelMember
    let key : Cell := ((horizontal : Int), (vertical : Int))
    have represented := lookupRepresents horizontal vertical
      horizontalBound verticalBound
    cases lookupValue : assignments.lookup key with
    | none =>
        have blank : drawing.indexedCellType horizontal vertical = .blank := by
          rw [represented, lookupValue]
          rfl
        rw [blank] at pixelTypeMember
        simp [orthogonalCellPixels] at pixelTypeMember
    | some cellType =>
        have assignmentMember : (key, cellType) ∈ assignments :=
          PeriodicThreeDM.List.mem_of_lookup_eq_some lookupValue
        have cellTypeEquality :
            drawing.indexedCellType horizontal vertical = cellType := by
          rw [represented, lookupValue]
          rfl
        simp only [sparseExpandedMotif, List.mem_flatMap]
        refine ⟨(key, cellType), assignmentMember, ?_⟩
        simp only [sparseAssignmentPixels, List.mem_map]
        refine ⟨pixel, ?_, ?_⟩
        · rwa [← cellTypeEquality]
        · rw [sparseBlockOrigin_nat]

end Gadget
end LeanTrominoes
