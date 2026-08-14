/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripCompilerSize
import LeanTrominoes.PeriodicCNFFlatEncodingSize
import LeanTrominoes.PeriodicStripFlatEncoding
import LeanTrominoes.PartrecCellDecode

/-!
# Flat target-encoding size of the rectangular tromino compiler
-/

namespace LeanTrominoes

open Gadget

namespace Gadget

/-- Every motif cell field is bounded by the expanded drawing dimensions. -/
theorem PeriodicOrthogonalDrawing.periodicStrip_cellFields_sum_le
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (cell : Cell)
    (member : cell ∈ (drawing.periodicStrip tromino).motif) :
    (PeriodicStripFlatEncoding.cellFields cell).sum ≤
      12 * drawing.horizontalPeriod + 12 * drawing.verticalPeriod := by
  have bounds := expandedMotif_mem_fundamentalDomain
    tromino drawing cell member
  rcases cell with ⟨x, y⟩
  simp only [PeriodicStrip.InFundamentalDomain,
    PeriodicOrthogonalDrawing.periodicStrip,
    Nat.cast_mul, Nat.cast_ofNat] at bounds
  rcases bounds with ⟨xNonnegative, xBound, yNonnegative, yBound⟩
  cases x with
  | negSucc magnitude => omega
  | ofNat horizontal =>
      cases y with
      | negSucc magnitude => omega
      | ofNat vertical =>
          have horizontalBound :
              horizontal < 6 * drawing.horizontalPeriod := by
            apply Int.ofNat_lt.mp
            simpa using xBound
          have verticalBound :
              vertical < 6 * drawing.verticalPeriod := by
            apply Int.ofNat_lt.mp
            simpa using yBound
          simp only [PeriodicStripFlatEncoding.cellFields,
            List.sum_cons, List.sum_nil, Nat.add_zero,
            IntEncoding.encode_ofNat]
          omega

private theorem flatMap_cellFields_sum_le
    (cells : List Cell) (bound : Nat)
    (bounded : ∀ cell ∈ cells,
      (PeriodicStripFlatEncoding.cellFields cell).sum ≤ bound) :
    (cells.flatMap PeriodicStripFlatEncoding.cellFields).sum ≤
      cells.length * bound := by
  induction cells with
  | nil => simp
  | cons cell cells induction =>
      simp only [List.flatMap_cons, List.sum_append, List.length_cons]
      have head := bounded cell (by simp)
      have tail := induction fun member memberMem =>
        bounded member (by simp [memberMem])
      calc
        (PeriodicStripFlatEncoding.cellFields cell).sum +
            (cells.flatMap PeriodicStripFlatEncoding.cellFields).sum ≤
          bound + cells.length * bound := Nat.add_le_add head tail
        _ = cells.length * bound + bound := Nat.add_comm _ _
        _ = (cells.length + 1) * bound := by
          rw [Nat.add_mul]
          simp

/-- The sum of all flat natural fields has an explicit polynomial bound in
the drawing dimensions and motif length. -/
theorem PeriodicOrthogonalDrawing.periodicStrip_stripFields_sum_le
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing) :
    (PeriodicStripFlatEncoding.stripFields
      (drawing.periodicStrip tromino)).sum ≤
      6 * drawing.verticalPeriod + 6 * drawing.horizontalPeriod +
        (drawing.periodicStrip tromino).motif.length +
        (drawing.periodicStrip tromino).motif.length *
          (12 * drawing.horizontalPeriod +
            12 * drawing.verticalPeriod) := by
  have motifFields := flatMap_cellFields_sum_le
    (drawing.periodicStrip tromino).motif
    (12 * drawing.horizontalPeriod + 12 * drawing.verticalPeriod)
    (fun cell member =>
      drawing.periodicStrip_cellFields_sum_le tromino cell member)
  unfold PeriodicStripFlatEncoding.stripFields
  simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  change
    6 * drawing.verticalPeriod +
        (6 * drawing.horizontalPeriod +
          (drawing.periodicStrip tromino).motif.length) +
        ((drawing.periodicStrip tromino).motif.flatMap
          PeriodicStripFlatEncoding.cellFields).sum ≤ _
  calc
    _ ≤ 6 * drawing.verticalPeriod +
          (6 * drawing.horizontalPeriod +
            (drawing.periodicStrip tromino).motif.length) +
          (drawing.periodicStrip tromino).motif.length *
            (12 * drawing.horizontalPeriod +
              12 * drawing.verticalPeriod) :=
      Nat.add_le_add_left motifFields _
    _ = _ := by omega

/-- Flat binary output length, before eliminating motif length, is bounded by
field sum plus field count. -/
theorem PeriodicOrthogonalDrawing.periodicStrip_flatEncoding_length_le
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing) :
    (PeriodicStripFlatEncoding.finEncoding.encode
      (drawing.periodicStrip tromino)).length ≤
      (6 * drawing.verticalPeriod + 6 * drawing.horizontalPeriod +
        (drawing.periodicStrip tromino).motif.length +
        (drawing.periodicStrip tromino).motif.length *
          (12 * drawing.horizontalPeriod +
            12 * drawing.verticalPeriod)) +
      (3 + 2 * (drawing.periodicStrip tromino).motif.length) := by
  have encoded :=
    PeriodicCNFFlatEncoding.encodeNatFields_length_le_sum_add_length
      (PeriodicStripFlatEncoding.stripFields
        (drawing.periodicStrip tromino))
  have fields := drawing.periodicStrip_stripFields_sum_le tromino
  have fieldCount := PeriodicStripFlatEncoding.stripFields_length
    (drawing.periodicStrip tromino)
  change
    (PeriodicCNFFlatEncoding.encodeNatFields
      (PeriodicStripFlatEncoding.stripFields
        (drawing.periodicStrip tromino))).length ≤ _
  calc
    _ ≤ (PeriodicStripFlatEncoding.stripFields
          (drawing.periodicStrip tromino)).sum +
        (PeriodicStripFlatEncoding.stripFields
          (drawing.periodicStrip tromino)).length := encoded
    _ ≤ (6 * drawing.verticalPeriod + 6 * drawing.horizontalPeriod +
          (drawing.periodicStrip tromino).motif.length +
          (drawing.periodicStrip tromino).motif.length *
            (12 * drawing.horizontalPeriod +
              12 * drawing.verticalPeriod)) +
        (3 + 2 * (drawing.periodicStrip tromino).motif.length) := by
      rw [fieldCount]
      exact Nat.add_le_add_right fields _

end Gadget

namespace PeriodicThreeDM
namespace NormalizationCompiler

/-- Explicit polynomial budget for the final flat tromino-strip encoding. -/
def stripFlatEncodingBudget (period : Nat) : Nat :=
  let height := 3 * period + 1
  let motifBound := period * height * 36
  (6 * height + 6 * period + motifBound +
      motifBound * (12 * period + 12 * height)) +
    (3 + 2 * motifBound)

/-- The target flat encoding produced after rectangular normalization has
length polynomial in the normalization period. -/
theorem compileStrip_periodicStrip_flatEncoding_length_le
    (tromino : Tromino) (input : Input) :
    (PeriodicStripFlatEncoding.finEncoding.encode
      ((compileStrip input).periodicStrip tromino)).length ≤
      stripFlatEncodingBudget (finalNormalizationPeriod input) := by
  have encoded :=
    (compileStrip input).periodicStrip_flatEncoding_length_le tromino
  have motif := compileStrip_periodicStrip_motif_length_le tromino input
  have scaledMotif :
      ((compileStrip input).periodicStrip tromino).motif.length *
          (12 * finalNormalizationPeriod input +
            12 * finalStripHeight input) ≤
        (finalNormalizationPeriod input *
          finalStripHeight input * 36) *
          (12 * finalNormalizationPeriod input +
            12 * finalStripHeight input) :=
    Nat.mul_le_mul_right _ motif
  change _ ≤ stripFlatEncodingBudget (finalNormalizationPeriod input)
  simp only [compileStrip_horizontalPeriod,
    compileStrip_verticalPeriod] at encoded
  simp only [finalStripHeight] at motif scaledMotif encoded ⊢
  unfold stripFlatEncodingBudget
  dsimp only
  omega

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
