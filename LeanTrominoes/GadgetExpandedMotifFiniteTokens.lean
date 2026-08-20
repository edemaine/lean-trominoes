/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetPixelFiniteTokens
import LeanTrominoes.GadgetReductionComputability

/-! # Prepared finite-token stream for an expanded gadget motif

This file lifts the affine token block for one bounded local pixel through
the exact natural-range loops used by `computableExpandedMotif`.  Its final
theorem says that a fixed finite block expansion produces the counted token
stream for an arbitrary drawing.
-/

namespace LeanTrominoes
namespace GadgetExpandedMotifFiniteTokens

open Gadget
open GadgetPixelFiniteTokens

/-- Normalize an integer known to lie in `[0, 6)` to its finite coordinate. -/
def boundedCoordinate (coordinate : Int) : Fin 6 :=
  ⟨coordinate.toNat % 6, Nat.mod_lt _ (by decide)⟩

/-- Normalize both coordinates of a local paper pixel. -/
def boundedPixel (pixel : Cell) : Fin 6 × Fin 6 :=
  (boundedCoordinate pixel.1, boundedCoordinate pixel.2)

theorem boundedCoordinate_val_eq (coordinate : Int)
    (nonnegative : 0 ≤ coordinate) (upper : coordinate < 6) :
    (boundedCoordinate coordinate).val = coordinate.toNat := by
  unfold boundedCoordinate
  apply Nat.mod_eq_of_lt
  omega

/-- Every pixel in a Figure 11/12 mask lies in its fixed local window. -/
theorem orthogonalCellPixel_bounds (tromino : Tromino)
    (cellType : OrthogonalCellType) (pixel : Cell)
    (member : pixel ∈ orthogonalCellPixels tromino cellType) :
    0 ≤ pixel.1 ∧ pixel.1 < 6 ∧ 0 ≤ pixel.2 ∧ pixel.2 < 6 := by
  have regionMember :
      pixel ∈ (orthogonalCellGadget tromino cellType).region := by
    simpa [orthogonalCellGadget, paperGadget] using member
  have windowMember :=
    orthogonalCellGadget_wellFormed tromino cellType regionMember
  simp only [Gadget.window, orthogonalCellGadget, paperGadget] at windowMember
  exact (mem_rectangleCells_iff 6 6 pixel).mp windowMember

theorem localCell_boundedPixel_eq (tromino : Tromino)
    (cellType : OrthogonalCellType) (pixel : Cell)
    (member : pixel ∈ orthogonalCellPixels tromino cellType) :
    localCell (boundedPixel pixel) = pixel := by
  have bounds := orthogonalCellPixel_bounds tromino cellType pixel member
  apply Prod.ext
  · change ((boundedCoordinate pixel.1).val : Int) = pixel.1
    rw [boundedCoordinate_val_eq pixel.1 bounds.1 bounds.2.1]
    exact Int.toNat_of_nonneg bounds.1
  · change ((boundedCoordinate pixel.2).val : Int) = pixel.2
    rw [boundedCoordinate_val_eq pixel.2 bounds.2.2.1 bounds.2.2.2]
    exact Int.toNat_of_nonneg bounds.2.2.1

/-- Flattening prepared pieces commutes with expansion and counted blocks. -/
theorem expand_flatMap_countedFieldBlocks
    {α : Type*} (values : List α)
    (prepared : α → List GadgetPixelFiniteTokens.Token)
    (blocks : α → List (List Nat))
    (each : ∀ value ∈ values,
      expand (prepared value) =
        CountedUnaryFieldTokens.countedFieldBlocks (blocks value)) :
    expand (values.flatMap prepared) =
      CountedUnaryFieldTokens.countedFieldBlocks
        (values.flatMap blocks) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [List.flatMap_cons, expand_append, each value (by simp),
        List.flatMap_cons]
      unfold CountedUnaryFieldTokens.countedFieldBlocks
      rw [List.flatMap_append]
      congr 1
      exact induction fun other member => each other (by simp [member])

/-- Prepared finite tokens for every pixel in one indexed drawing block. -/
def preparedIndexedExpandedBlockPixels
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (horizontal vertical : Nat) : List GadgetPixelFiniteTokens.Token :=
  (orthogonalCellPixels tromino
      (drawing.indexedCellType horizontal vertical)).flatMap fun pixel =>
    pixelBlock horizontal vertical (boundedPixel pixel)

theorem expand_preparedIndexedExpandedBlockPixels
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (horizontal vertical : Nat) :
    expand (preparedIndexedExpandedBlockPixels
        tromino drawing horizontal vertical) =
      CountedUnaryFieldTokens.countedFieldBlocks
        ((drawing.indexedExpandedBlockPixels
            tromino horizontal vertical).map
          PeriodicStripFlatEncoding.cellFields) := by
  let cellType := drawing.indexedCellType horizontal vertical
  let pixels := orthogonalCellPixels tromino cellType
  have expanded := expand_flatMap_countedFieldBlocks pixels
    (fun pixel => pixelBlock horizontal vertical (boundedPixel pixel))
    (fun pixel =>
      [PeriodicStripFlatEncoding.cellFields
        (Cell.add
          (PeriodicOrthogonalDrawing.blockOrigin horizontal vertical)
          pixel)])
    (fun pixel member => by
      rw [expand_pixelBlock]
      rw [localCell_boundedPixel_eq tromino cellType pixel member]
      simp [CountedUnaryFieldTokens.countedFieldBlocks])
  unfold preparedIndexedExpandedBlockPixels
  change expand (pixels.flatMap fun pixel =>
      pixelBlock horizontal vertical (boundedPixel pixel)) = _
  rw [expanded]
  unfold PeriodicOrthogonalDrawing.indexedExpandedBlockPixels
  change CountedUnaryFieldTokens.countedFieldBlocks
      (pixels.flatMap fun pixel =>
        [PeriodicStripFlatEncoding.cellFields
          (Cell.add
            (PeriodicOrthogonalDrawing.blockOrigin horizontal vertical)
            pixel)]) =
    CountedUnaryFieldTokens.countedFieldBlocks
      ((pixels.map fun pixel =>
        Cell.add
          (PeriodicOrthogonalDrawing.blockOrigin horizontal vertical)
          pixel).map PeriodicStripFlatEncoding.cellFields)
  congr 1
  induction pixels with
  | nil => rfl
  | cons pixel pixels induction => simp [induction]

/-- Prepared natural-range loop for all gadget pixels in a drawing. -/
def preparedExpandedMotif (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    List GadgetPixelFiniteTokens.Token :=
  (List.range drawing.horizontalPeriod).flatMap fun horizontal =>
    (List.range drawing.verticalPeriod).flatMap fun vertical =>
      preparedIndexedExpandedBlockPixels
        tromino drawing horizontal vertical

@[simp] theorem expand_preparedExpandedMotif (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    expand (preparedExpandedMotif tromino drawing) =
      CountedUnaryFieldTokens.countedFieldBlocks
        ((drawing.computableExpandedMotif tromino).map
          PeriodicStripFlatEncoding.cellFields) := by
  unfold preparedExpandedMotif
    PeriodicOrthogonalDrawing.computableExpandedMotif
  rw [expand_flatMap_countedFieldBlocks
    (List.range drawing.horizontalPeriod)
    (fun horizontal =>
      (List.range drawing.verticalPeriod).flatMap fun vertical =>
        preparedIndexedExpandedBlockPixels
          tromino drawing horizontal vertical)
    (fun horizontal =>
      (List.range drawing.verticalPeriod).flatMap fun vertical =>
        (drawing.indexedExpandedBlockPixels
            tromino horizontal vertical).map
          PeriodicStripFlatEncoding.cellFields)]
  · congr 1
    simp [List.map_flatMap]
  · intro horizontal _
    exact expand_flatMap_countedFieldBlocks
      (List.range drawing.verticalPeriod)
      (fun vertical => preparedIndexedExpandedBlockPixels
        tromino drawing horizontal vertical)
      (fun vertical =>
        (drawing.indexedExpandedBlockPixels
            tromino horizontal vertical).map
          PeriodicStripFlatEncoding.cellFields)
      (fun vertical _ =>
        expand_preparedIndexedExpandedBlockPixels
          tromino drawing horizontal vertical)

/-- Width and period header followed by the prepared expanded motif. -/
def preparedStripTokens (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    List GadgetPixelFiniteTokens.Token :=
  headerField drawing.verticalPeriod ++
    headerField drawing.horizontalPeriod ++
      preparedExpandedMotif tromino drawing

/-- Fixed expansion recovers the exact counted strip token layout. -/
theorem expand_preparedStripTokens (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    expand (preparedStripTokens tromino drawing) =
      CountedUnaryFieldTokens.fields
          [6 * drawing.verticalPeriod, 6 * drawing.horizontalPeriod] ++
        CountedUnaryFieldTokens.countedFieldBlocks
          ((drawing.computableExpandedMotif tromino).map
            PeriodicStripFlatEncoding.cellFields) := by
  unfold preparedStripTokens
  rw [expand_append, expand_append, expand_headerField,
    expand_headerField, expand_preparedExpandedMotif]
  simp [CountedUnaryFieldTokens.fields, List.append_assoc]

end GadgetExpandedMotifFiniteTokens
end LeanTrominoes
