/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenMachineExecution

/-! # Output-length bounds for sparse assignment-token parsing -/

namespace LeanTrominoes

namespace GadgetSparseAssignmentTokenMachine

theorem pixelBlock_length (horizontal vertical : Nat)
    (pixel : LocalPixel) :
    (GadgetPixelFiniteTokens.pixelBlock horizontal vertical pixel).length =
      horizontal + vertical + 5 := by
  simp [GadgetPixelFiniteTokens.pixelBlock,
    GadgetPixelFiniteTokens.coordinateField]
  omega

/-- Prepared output for a pixel suffix is no longer than its exact cursor
allowance. -/
theorem preparedPixels_length_le_pixelsTime (horizontal vertical : Nat)
    (pixels : List LocalPixel) :
    (preparedPixels horizontal vertical pixels).length ≤
      pixelsTime horizontal vertical pixels := by
  induction pixels with
  | nil => simp [preparedPixels, pixelsTime]
  | cons pixel pixels induction =>
      rw [show preparedPixels horizontal vertical (pixel :: pixels) =
          GadgetPixelFiniteTokens.pixelBlock horizontal vertical pixel ++
            preparedPixels horizontal vertical pixels by rfl,
        List.length_append, pixelsTime_cons]
      rw [pixelBlock_length]
      unfold pixelTime
      omega

theorem preparedNatAssignmentPixels_length_le_pixelsTime
    (tromino : Tromino) (cellType : Gadget.OrthogonalCellType)
    (horizontal vertical : Nat) :
    (GadgetSparseAssignmentTokens.preparedNatAssignmentPixels tromino
      horizontal vertical cellType).length ≤
        pixelsTime horizontal vertical (boundedPixels tromino cellType) := by
  rw [← preparedPixels_boundedPixels]
  exact preparedPixels_length_le_pixelsTime horizontal vertical _

/-- The semantic output suffix is bounded by the exact scan allowance on
every (possibly malformed) input word. -/
theorem phaseExpand_length_le_scanTime (tromino : Tromino) (phase : Phase)
    (horizontal vertical : Nat) (tokens : List InputToken) :
    (phaseExpand tromino phase horizontal vertical tokens).length ≤
      scanTime tromino phase horizontal vertical tokens := by
  induction tokens generalizing phase horizontal vertical with
  | nil =>
      cases phase <;>
        simp [phaseExpand,
          GadgetSparseAssignmentTokens.expandAux, scanTime]
  | cons token tokens induction =>
      cases phase with
      | horizontal =>
          cases token with
          | coordinateUnit =>
              have rest := induction .horizontal (horizontal + 1) 0
              simpa [phaseExpand, phaseVertical,
                GadgetSparseAssignmentTokens.expandAux, scanTime] using
                rest.trans (Nat.le_add_right _ _)
          | fieldEnd =>
              have rest := induction .vertical horizontal 0
              simpa [phaseExpand, phaseVertical,
                GadgetSparseAssignmentTokens.expandAux, scanTime] using
                rest.trans (Nat.le_add_right _ _)
          | cellType cellType =>
              have rest := induction .horizontal 0 0
              have larger := rest.trans
                (Nat.le_add_right _ (horizontal + 2 + 1))
              simpa [phaseExpand, phaseVertical,
                GadgetSparseAssignmentTokens.expandAux, scanTime] using larger
      | vertical =>
          cases token with
          | coordinateUnit =>
              have rest := induction .vertical horizontal (vertical + 1)
              simpa [phaseExpand, phaseVertical,
                GadgetSparseAssignmentTokens.expandAux, scanTime] using
                rest.trans (Nat.le_add_right _ _)
          | fieldEnd =>
              have rest := induction .horizontal 0 0
              have larger := rest.trans
                (Nat.le_add_right _ (horizontal + vertical + 2 + 1))
              simpa [phaseExpand, phaseVertical,
                GadgetSparseAssignmentTokens.expandAux, scanTime] using larger
          | cellType cellType =>
              have rest := induction .horizontal 0 0
              have pixels :=
                preparedNatAssignmentPixels_length_le_pixelsTime tromino
                  cellType horizontal vertical
              have rest' :
                  (GadgetSparseAssignmentTokens.expandAux tromino .horizontal
                    0 0 tokens).length ≤
                    scanTime tromino .horizontal 0 0 tokens := by
                simpa [phaseExpand, phaseVertical] using rest
              simp only [phaseExpand, phaseVertical,
                GadgetSparseAssignmentTokens.expandAux, List.length_append,
                scanTime]
              omega

theorem expand_length_le_scanTime (tromino : Tromino)
    (tokens : List InputToken) :
    (GadgetSparseAssignmentTokens.expand tromino tokens).length ≤
      scanTime tromino .horizontal 0 0 tokens := by
  simpa [GadgetSparseAssignmentTokens.expand, phaseExpand, phaseVertical]
    using phaseExpand_length_le_scanTime tromino .horizontal 0 0 tokens

end GadgetSparseAssignmentTokenMachine
end LeanTrominoes
