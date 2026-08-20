/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetExpandedMotifFiniteTokens
import LeanTrominoes.GadgetSparseExpandedMotif

/-! # Prepared finite tokens for sparse assignment motifs -/

namespace LeanTrominoes
namespace GadgetSparseExpandedMotifFiniteTokens

open Gadget
open GadgetPixelFiniteTokens
open GadgetExpandedMotifFiniteTokens

/-- Prepared pixel blocks contributed by one sparse drawing-cell assignment. -/
def preparedSparseAssignmentPixels (tromino : Tromino)
    (assignment : Cell × OrthogonalCellType) : List Token :=
  (orthogonalCellPixels tromino assignment.2).flatMap fun pixel =>
    pixelBlock assignment.1.1.toNat assignment.1.2.toNat
      (boundedPixel pixel)

/-- Prepared pixel blocks for a complete sparse assignment list. -/
def preparedSparseExpandedMotif (tromino : Tromino)
    (assignments : List (Cell × OrthogonalCellType)) : List Token :=
  assignments.flatMap (preparedSparseAssignmentPixels tromino)

theorem blockOrigin_toNat_eq_sparseBlockOrigin
    (location : Cell) (horizontalNonnegative : 0 ≤ location.1)
    (verticalNonnegative : 0 ≤ location.2) :
    PeriodicOrthogonalDrawing.blockOrigin location.1.toNat location.2.toNat =
      sparseBlockOrigin location := by
  rw [← sparseBlockOrigin_nat]
  congr 1
  apply Prod.ext
  · exact Int.toNat_of_nonneg horizontalNonnegative
  · exact Int.toNat_of_nonneg verticalNonnegative

/-- Fixed expansion of one prepared sparse assignment gives exactly its
counted gadget-pixel fields. -/
theorem expand_preparedSparseAssignmentPixels
    (tromino : Tromino) (assignment : Cell × OrthogonalCellType)
    (horizontalNonnegative : 0 ≤ assignment.1.1)
    (verticalNonnegative : 0 ≤ assignment.1.2) :
    expand (preparedSparseAssignmentPixels tromino assignment) =
      CountedUnaryFieldTokens.countedFieldBlocks
        ((sparseAssignmentPixels tromino assignment).map
          PeriodicStripFlatEncoding.cellFields) := by
  let cellType := assignment.2
  let pixels := orthogonalCellPixels tromino cellType
  have expanded := expand_flatMap_countedFieldBlocks pixels
    (fun pixel => pixelBlock assignment.1.1.toNat assignment.1.2.toNat
      (boundedPixel pixel))
    (fun pixel =>
      [PeriodicStripFlatEncoding.cellFields
        (Cell.add (sparseBlockOrigin assignment.1) pixel)])
    (fun pixel member => by
      rw [expand_pixelBlock]
      rw [localCell_boundedPixel_eq tromino cellType pixel member]
      rw [blockOrigin_toNat_eq_sparseBlockOrigin assignment.1
        horizontalNonnegative verticalNonnegative]
      simp [CountedUnaryFieldTokens.countedFieldBlocks])
  unfold preparedSparseAssignmentPixels
  change expand (pixels.flatMap fun pixel =>
      pixelBlock assignment.1.1.toNat assignment.1.2.toNat
        (boundedPixel pixel)) = _
  rw [expanded]
  unfold sparseAssignmentPixels
  change CountedUnaryFieldTokens.countedFieldBlocks
      (pixels.flatMap fun pixel =>
        [PeriodicStripFlatEncoding.cellFields
          (Cell.add (sparseBlockOrigin assignment.1) pixel)]) =
    CountedUnaryFieldTokens.countedFieldBlocks
      ((pixels.map fun pixel =>
        Cell.add (sparseBlockOrigin assignment.1) pixel).map
          PeriodicStripFlatEncoding.cellFields)
  congr 1
  induction pixels with
  | nil => rfl
  | cons pixel pixels induction => simp [induction]

/-- Fixed expansion recovers the counted motif stream for any sparse list
whose assignment coordinates are nonnegative. -/
theorem expand_preparedSparseExpandedMotif
    (tromino : Tromino)
    (assignments : List (Cell × OrthogonalCellType))
    (nonnegative : ∀ assignment ∈ assignments,
      0 ≤ assignment.1.1 ∧ 0 ≤ assignment.1.2) :
    expand (preparedSparseExpandedMotif tromino assignments) =
      CountedUnaryFieldTokens.countedFieldBlocks
        ((sparseExpandedMotif tromino assignments).map
          PeriodicStripFlatEncoding.cellFields) := by
  unfold preparedSparseExpandedMotif sparseExpandedMotif
  rw [expand_flatMap_countedFieldBlocks assignments
    (preparedSparseAssignmentPixels tromino)
    (fun assignment =>
      (sparseAssignmentPixels tromino assignment).map
        PeriodicStripFlatEncoding.cellFields)]
  · congr 1
    simp [List.map_flatMap]
  · intro assignment member
    exact expand_preparedSparseAssignmentPixels tromino assignment
      (nonnegative assignment member).1
      (nonnegative assignment member).2

/-- Prepared height and period fields followed by a sparse gadget motif. -/
def preparedSparseStripTokens (tromino : Tromino)
    (verticalPeriod horizontalPeriod : Nat)
    (assignments : List (Cell × OrthogonalCellType)) : List Token :=
  headerField verticalPeriod ++ headerField horizontalPeriod ++
    preparedSparseExpandedMotif tromino assignments

theorem expand_preparedSparseStripTokens
    (tromino : Tromino) (verticalPeriod horizontalPeriod : Nat)
    (assignments : List (Cell × OrthogonalCellType))
    (nonnegative : ∀ assignment ∈ assignments,
      0 ≤ assignment.1.1 ∧ 0 ≤ assignment.1.2) :
    expand (preparedSparseStripTokens tromino verticalPeriod horizontalPeriod
        assignments) =
      CountedUnaryFieldTokens.fields
          [6 * verticalPeriod, 6 * horizontalPeriod] ++
        CountedUnaryFieldTokens.countedFieldBlocks
          ((sparseExpandedMotif tromino assignments).map
            PeriodicStripFlatEncoding.cellFields) := by
  unfold preparedSparseStripTokens
  rw [expand_append, expand_append, expand_headerField,
    expand_headerField,
    expand_preparedSparseExpandedMotif tromino assignments nonnegative]
  simp [CountedUnaryFieldTokens.fields, List.append_assoc]

end GadgetSparseExpandedMotifFiniteTokens
end LeanTrominoes
