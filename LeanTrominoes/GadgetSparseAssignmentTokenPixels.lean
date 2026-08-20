/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenMachineCoordinateExecution

/-! # Finite pixel-list data for sparse assignment-token expansion -/

namespace LeanTrominoes

namespace GadgetSparseAssignmentTokenMachine

open Gadget

/-- The Figure 11/12 mask represented in the machine's finite local alphabet. -/
def boundedPixels (tromino : Tromino) (cellType : OrthogonalCellType) :
    List LocalPixel :=
  (orthogonalCellPixels tromino cellType).map
    GadgetExpandedMotifFiniteTokens.boundedPixel

theorem pixelAt?_eq (tromino : Tromino) (cellType : OrthogonalCellType)
    (index : PixelIndex) :
    pixelAt? tromino cellType index =
      (boundedPixels tromino cellType)[index.val]? :=
  rfl

/-- Every local mask fits in the 36 positions of its `6 × 6` window. -/
theorem boundedPixels_length_le (tromino : Tromino)
    (cellType : OrthogonalCellType) :
    (boundedPixels tromino cellType).length ≤ 36 := by
  cases tromino <;>
    cases cellType with
    | blank => native_decide
    | wire axis color => cases axis <;> cases color <;> native_decide
    | bend bend color => cases bend <;> cases color <;> native_decide
    | monochromaticVertex color => cases color <;> native_decide
    | trichromaticVertex order => cases order <;> native_decide

/-- Prepared blocks for an already bounded local pixel list. -/
def preparedPixels (horizontal vertical : Nat) (pixels : List LocalPixel) :
    List OutputToken :=
  pixels.flatMap fun pixel =>
    GadgetPixelFiniteTokens.pixelBlock horizontal vertical pixel

/-- Bounding the fixed mask before flattening preserves the prepared stream. -/
theorem preparedPixels_boundedPixels (tromino : Tromino)
    (cellType : OrthogonalCellType) (horizontal vertical : Nat) :
    preparedPixels horizontal vertical (boundedPixels tromino cellType) =
      GadgetSparseAssignmentTokens.preparedNatAssignmentPixels tromino
        horizontal vertical cellType := by
  unfold preparedPixels boundedPixels
    GadgetSparseAssignmentTokens.preparedNatAssignmentPixels
  generalize orthogonalCellPixels tromino cellType = pixels
  induction pixels with
  | nil => rfl
  | cons pixel pixels induction => simp [induction]

/-- Exact transition allowance for one local pixel, including both copied
coordinates and the initial cell marker. -/
def pixelTime (horizontal vertical : Nat) : Nat :=
  2 * horizontal + 2 * vertical + 5

/-- Exact allowance for a suffix of local pixels and its final empty-cursor
transition. -/
def pixelsTime (horizontal vertical : Nat) : List LocalPixel → Nat
  | [] => 1
  | _ :: pixels => pixelTime horizontal vertical +
      pixelsTime horizontal vertical pixels

@[simp] theorem pixelsTime_nil (horizontal vertical : Nat) :
    pixelsTime horizontal vertical [] = 1 := rfl

@[simp] theorem pixelsTime_cons (horizontal vertical : Nat)
    (pixel : LocalPixel) (pixels : List LocalPixel) :
    pixelsTime horizontal vertical (pixel :: pixels) =
      pixelTime horizontal vertical + pixelsTime horizontal vertical pixels :=
  rfl

theorem pixelsTime_eq (horizontal vertical : Nat)
    (pixels : List LocalPixel) :
    pixelsTime horizontal vertical pixels =
      pixels.length * pixelTime horizontal vertical + 1 := by
  induction pixels with
  | nil => simp [pixelsTime]
  | cons pixel pixels induction =>
      simp only [pixelsTime, List.length_cons, Nat.succ_mul, induction]
      omega

end GadgetSparseAssignmentTokenMachine
end LeanTrominoes
