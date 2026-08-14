/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripCompiler
import LeanTrominoes.GadgetStripSubstitution

/-!
# Size bounds for the rectangular drawing and tromino motif
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM
namespace NormalizationCompiler

/-- The normalization period is positive for every finite compiler input. -/
theorem finalNormalizationPeriod_pos (input : Input) :
    0 < finalNormalizationPeriod input := by
  simp [finalNormalizationPeriod, vertexNormalizationScaleNat,
    contractedDrawing, PeriodicGridDrawing.gridSize]

/-- The rectangular row-major compiler stores exactly one cell per position. -/
theorem finalStripCellTypes_length (input : Input) :
    (finalStripCellTypes input).length =
      finalStripHeight input * finalNormalizationPeriod input := by
  unfold finalStripCellTypes rowMajorList
  rw [List.length_flatMap]
  simp

theorem compiledStripCellTypes_length (input : Input) :
    (compiledStripCellTypes input).length =
      finalStripHeight input * finalNormalizationPeriod input := by
  exact finalStripCellTypes_length input

/-- The compiled drawing advertises the intended positive width. -/
theorem compileStrip_horizontalPeriod (input : Input) :
    (compileStrip input).horizontalPeriod =
      finalNormalizationPeriod input := by
  unfold Gadget.PeriodicOrthogonalDrawing.horizontalPeriod compileStrip
  rw [Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (finalNormalizationPeriod_pos input)))]

/-- Its vertical period is the two-seam rectangular height. -/
theorem compileStrip_verticalPeriod (input : Input) :
    (compileStrip input).verticalPeriod = finalStripHeight input := by
  rfl

end NormalizationCompiler
end PeriodicThreeDM

namespace Gadget

/-- Every fixed Figure 11/12 mask occupies at most its `6 × 6` window. -/
theorem orthogonalCellPixels_length_le_36
    (tromino : Tromino) (cellType : OrthogonalCellType) :
    (orthogonalCellPixels tromino cellType).length ≤ 36 := by
  cases tromino <;>
    cases cellType with
    | blank => native_decide
    | wire axis color => cases axis <;> cases color <;> native_decide
    | bend bend color => cases bend <;> cases color <;> native_decide
    | monochromaticVertex color => cases color <;> native_decide
    | trichromaticVertex order => cases order <;> native_decide

private theorem flatMap_length_le
    {α β : Type*} (values : List α) (function : α → List β)
    (bound : Nat)
    (bounded : ∀ value ∈ values, (function value).length ≤ bound) :
    (values.flatMap function).length ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value values induction =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have head := bounded value (by simp)
      have tail := induction fun member memberMem =>
        bounded member (by simp [memberMem])
      calc
        (function value).length + (values.flatMap function).length ≤
            bound + values.length * bound := Nat.add_le_add head tail
        _ = values.length * bound + bound := Nat.add_comm _ _
        _ = (values.length + 1) * bound := by
          rw [Nat.add_mul]
          simp

/-- Gadget substitution emits at most 36 motif cells per drawing position. -/
theorem PeriodicOrthogonalDrawing.expandedMotif_length_le
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing) :
    (drawing.expandedMotif tromino).length ≤
      drawing.horizontalPeriod * drawing.verticalPeriod * 36 := by
  rw [← drawing.computableExpandedMotif_eq tromino]
  unfold PeriodicOrthogonalDrawing.computableExpandedMotif
  have blockBound : ∀ horizontal : Nat,
      horizontal ∈ List.range drawing.horizontalPeriod →
      ((List.range drawing.verticalPeriod).flatMap fun vertical =>
        drawing.indexedExpandedBlockPixels tromino horizontal vertical).length ≤
        drawing.verticalPeriod * 36 := by
    intro horizontal _
    have inner := flatMap_length_le
      (List.range drawing.verticalPeriod)
        (fun vertical =>
          drawing.indexedExpandedBlockPixels tromino horizontal vertical) 36
        (fun vertical _ => by
          simp only [PeriodicOrthogonalDrawing.indexedExpandedBlockPixels,
            List.length_map]
          exact orthogonalCellPixels_length_le_36 tromino
            (drawing.indexedCellType horizontal vertical))
    simpa only [List.length_range] using inner
  have outer := flatMap_length_le
    (List.range drawing.horizontalPeriod)
    (fun horizontal =>
      (List.range drawing.verticalPeriod).flatMap fun vertical =>
        drawing.indexedExpandedBlockPixels tromino horizontal vertical)
    (drawing.verticalPeriod * 36) blockBound
  simpa only [List.length_range, Nat.mul_assoc] using outer

/-- The complete target strip motif has the same quadratic position bound. -/
theorem PeriodicOrthogonalDrawing.periodicStrip_motif_length_le
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing) :
    (drawing.periodicStrip tromino).motif.length ≤
      drawing.horizontalPeriod * drawing.verticalPeriod * 36 :=
  drawing.expandedMotif_length_le tromino

end Gadget

namespace PeriodicThreeDM
namespace NormalizationCompiler

/-- Applied to the rectangular compiler, gadget motif size is quadratic in
the final normalization period. -/
theorem compileStrip_periodicStrip_motif_length_le
    (tromino : Tromino) (input : Input) :
    ((compileStrip input).periodicStrip tromino).motif.length ≤
      finalNormalizationPeriod input * finalStripHeight input * 36 := by
  simpa [compileStrip_horizontalPeriod, compileStrip_verticalPeriod] using
    (compileStrip input).periodicStrip_motif_length_le tromino

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
