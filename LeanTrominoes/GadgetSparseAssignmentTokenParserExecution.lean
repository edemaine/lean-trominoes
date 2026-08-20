/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenParserData

/-! # Exact total parser execution for sparse assignment tokens -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseAssignmentTokenMachine

open Gadget

/-- Clear canonical coordinate counters and resume horizontal scanning. -/
def clearToScan_evalsInTime (tromino : Tromino)
    (input : List InputToken) (horizontal vertical : Nat)
    (outputReverse output : List OutputToken) :
    EvalsToInTime (TM2.step (program tromino))
      (clearHorizontalCfg .scan
        (activeData input horizontal vertical outputReverse output))
      (some (scanHorizontalCfg
        (activeData input 0 0 outputReverse output)))
      (horizontal + vertical + 2) := by
  have run := clear_evalsInTime tromino .scan
    (List.replicate horizontal ()) (List.replicate vertical ())
    (activeData input horizontal vertical outputReverse output) rfl rfl
  simpa [activeData, afterClear, scanHorizontalCfg] using run

/-- Clear canonical coordinate counters and enter final reversal. -/
def clearToReverse_evalsInTime (tromino : Tromino)
    (input : List InputToken) (horizontal vertical : Nat)
    (outputReverse output : List OutputToken) :
    EvalsToInTime (TM2.step (program tromino))
      (clearHorizontalCfg .reverseOutput
        (activeData input horizontal vertical outputReverse output))
      (some (reverseOutputCfg
        (activeData input 0 0 outputReverse output)))
      (horizontal + vertical + 2) := by
  have run := clear_evalsInTime tromino .reverseOutput
    (List.replicate horizontal ()) (List.replicate vertical ())
    (activeData input horizontal vertical outputReverse output) rfl rfl
  simpa [activeData, afterClear, reverseOutputCfg] using run

/-- From a parsed finite cell type, expand its complete fixed mask, clear both
coordinates, and resume at the next record. -/
def finishCell_evalsInTime (tromino : Tromino)
    (cellType : OrthogonalCellType) (state : State)
    (input : List InputToken) (horizontal vertical : Nat)
    (outputReverse output : List OutputToken) :
    EvalsToInTime (TM2.step (program tromino))
      (beginPixelsCfg cellType state
        (activeData input horizontal vertical outputReverse output))
      (some (scanHorizontalCfg
        (activeData input 0 0
          ((GadgetSparseAssignmentTokens.preparedNatAssignmentPixels tromino
              horizontal vertical cellType).reverse ++ outputReverse) output)))
      (1 + pixelsTime horizontal vertical (boundedPixels tromino cellType) +
        (horizontal + vertical + 2)) := by
  have first := oneStep (step_beginPixels tromino
    (activeData input horizontal vertical outputReverse output) cellType state)
  have pixels := completePixels_evalsInTime tromino cellType input
    horizontal vertical outputReverse output
  have throughPixels := EvalsToInTime.trans (TM2.step (program tromino))
    1 (pixelsTime horizontal vertical (boundedPixels tromino cellType))
    (beginPixelsCfg cellType state
      (activeData input horizontal vertical outputReverse output))
    (pixelStartCfg cellType firstPixelIndex
      (activeData input horizontal vertical outputReverse output))
    (some (clearHorizontalCfg .scan
      (activeData input horizontal vertical
        ((GadgetSparseAssignmentTokens.preparedNatAssignmentPixels tromino
            horizontal vertical cellType).reverse ++ outputReverse) output)))
    first pixels
  have cleared := clearToScan_evalsInTime tromino input horizontal vertical
    ((GadgetSparseAssignmentTokens.preparedNatAssignmentPixels tromino
      horizontal vertical cellType).reverse ++ outputReverse) output
  have whole := EvalsToInTime.trans (TM2.step (program tromino))
    (pixelsTime horizontal vertical (boundedPixels tromino cellType) + 1)
    (horizontal + vertical + 2)
    (beginPixelsCfg cellType state
      (activeData input horizontal vertical outputReverse output))
    (clearHorizontalCfg .scan
      (activeData input horizontal vertical
        ((GadgetSparseAssignmentTokens.preparedNatAssignmentPixels tromino
            horizontal vertical cellType).reverse ++ outputReverse) output))
    (some (scanHorizontalCfg
      (activeData input 0 0
        ((GadgetSparseAssignmentTokens.preparedNatAssignmentPixels tromino
            horizontal vertical cellType).reverse ++ outputReverse) output)))
    throughPixels cleared
  convert whole using 1
  omega

/-- The scan phases execute exactly the total semantic parser on every finite
token word, stopping immediately before final output reversal. -/
def scan_evalsInTime (tromino : Tromino) (phase : Phase)
    (horizontal vertical : Nat) (tokens : List InputToken)
    (outputReverse output : List OutputToken) :
    EvalsToInTime (TM2.step (program tromino))
      (phaseCfg phase
        (phaseData phase tokens horizontal vertical outputReverse output))
      (some (reverseOutputCfg
        (activeData [] 0 0
          ((phaseExpand tromino phase horizontal vertical tokens).reverse ++
            outputReverse) output)))
      (scanTime tromino phase horizontal vertical tokens) := by
  induction tokens generalizing phase horizontal vertical outputReverse with
  | nil =>
      cases phase with
      | horizontal =>
          let initial := activeData [] horizontal 0 outputReverse output
          have first := oneStep
            (step_scanHorizontal_nil tromino initial rfl)
          have cleared := clearToReverse_evalsInTime tromino [] horizontal 0
            outputReverse output
          have whole := EvalsToInTime.trans (TM2.step (program tromino))
            1 (horizontal + 0 + 2)
            (scanHorizontalCfg initial)
            (clearHorizontalCfg .reverseOutput initial)
            (some (reverseOutputCfg
              (activeData [] 0 0 outputReverse output))) first
            (by simpa [initial] using cleared)
          simpa [phaseCfg, phaseData, phaseVertical, phaseExpand,
            GadgetSparseAssignmentTokens.expandAux, scanTime, initial]
            using whole
      | vertical =>
          let initial := activeData [] horizontal vertical outputReverse output
          have first := oneStep (step_scanVertical_nil tromino initial rfl)
          have cleared := clearToReverse_evalsInTime tromino [] horizontal
            vertical outputReverse output
          have whole := EvalsToInTime.trans (TM2.step (program tromino))
            1 (horizontal + vertical + 2)
            (scanVerticalCfg initial)
            (clearHorizontalCfg .reverseOutput initial)
            (some (reverseOutputCfg
              (activeData [] 0 0 outputReverse output))) first
            (by simpa [initial] using cleared)
          simpa [phaseCfg, phaseData, phaseVertical, phaseExpand,
            GadgetSparseAssignmentTokens.expandAux, scanTime, initial]
            using whole
  | cons token tokens induction =>
      cases phase with
      | horizontal =>
          cases token with
          | coordinateUnit =>
              let initial := activeData (.coordinateUnit :: tokens)
                horizontal 0 outputReverse output
              let next := activeData tokens (horizontal + 1) 0
                outputReverse output
              have first := oneStep
                (step_scanHorizontal_coordinateUnit tromino initial tokens rfl)
              have first' : EvalsToInTime (TM2.step (program tromino))
                  (scanHorizontalCfg initial)
                  (some (scanHorizontalCfg next)) 1 := by
                simpa [initial, next, activeData, List.replicate_succ]
                  using first
              have rest := induction .horizontal (horizontal + 1) 0
                outputReverse
              have whole := EvalsToInTime.trans (TM2.step (program tromino))
                1 (scanTime tromino .horizontal (horizontal + 1) 0 tokens)
                (scanHorizontalCfg initial) (scanHorizontalCfg next)
                (some (reverseOutputCfg
                  (activeData [] 0 0
                    ((phaseExpand tromino .horizontal (horizontal + 1) 0
                      tokens).reverse ++ outputReverse) output))) first'
                (by simpa [phaseCfg, phaseData, phaseVertical, next] using rest)
              simpa [phaseCfg, phaseData, phaseVertical, phaseExpand,
                GadgetSparseAssignmentTokens.expandAux, scanTime, initial]
                using whole
          | fieldEnd =>
              let initial := activeData (.fieldEnd :: tokens)
                horizontal 0 outputReverse output
              let next := activeData tokens horizontal 0 outputReverse output
              have first := oneStep
                (step_scanHorizontal_fieldEnd tromino initial tokens rfl)
              have rest := induction .vertical horizontal 0 outputReverse
              have whole := EvalsToInTime.trans (TM2.step (program tromino))
                1 (scanTime tromino .vertical horizontal 0 tokens)
                (scanHorizontalCfg initial) (scanVerticalCfg next)
                (some (reverseOutputCfg
                  (activeData [] 0 0
                    ((phaseExpand tromino .vertical horizontal 0 tokens).reverse ++
                      outputReverse) output)))
                (by simpa [initial, next, activeData] using first)
                (by simpa [phaseCfg, phaseData, phaseVertical, next] using rest)
              simpa [phaseCfg, phaseData, phaseVertical, phaseExpand,
                GadgetSparseAssignmentTokens.expandAux, scanTime, initial]
                using whole
          | cellType cellType =>
              let initial := activeData (.cellType cellType :: tokens)
                horizontal 0 outputReverse output
              let afterInput := activeData tokens horizontal 0
                outputReverse output
              have first := oneStep
                (step_scanHorizontal_cellType tromino initial cellType tokens rfl)
              have cleared := clearToScan_evalsInTime tromino tokens horizontal 0
                outputReverse output
              have throughClear := EvalsToInTime.trans
                (TM2.step (program tromino)) 1 (horizontal + 0 + 2)
                (scanHorizontalCfg initial)
                (clearHorizontalCfg .scan afterInput)
                (some (scanHorizontalCfg
                  (activeData tokens 0 0 outputReverse output)))
                (by simpa [initial, afterInput, activeData] using first)
                (by simpa [afterInput] using cleared)
              have rest := induction .horizontal 0 0 outputReverse
              have whole := EvalsToInTime.trans (TM2.step (program tromino))
                (horizontal + 0 + 2 + 1)
                (scanTime tromino .horizontal 0 0 tokens)
                (scanHorizontalCfg initial)
                (scanHorizontalCfg (activeData tokens 0 0 outputReverse output))
                (some (reverseOutputCfg
                  (activeData [] 0 0
                    ((phaseExpand tromino .horizontal 0 0 tokens).reverse ++
                      outputReverse) output))) throughClear
                (by simpa [phaseCfg, phaseData, phaseVertical] using rest)
              convert whole using 1
              · rfl
              · rfl
              · change scanTime tromino .horizontal 0 0 tokens +
                    (horizontal + 2 + 1) =
                  scanTime tromino .horizontal 0 0 tokens +
                    (horizontal + 0 + 2 + 1)
                omega
      | vertical =>
          cases token with
          | coordinateUnit =>
              let initial := activeData (.coordinateUnit :: tokens)
                horizontal vertical outputReverse output
              let next := activeData tokens horizontal (vertical + 1)
                outputReverse output
              have first := oneStep
                (step_scanVertical_coordinateUnit tromino initial tokens rfl)
              have first' : EvalsToInTime (TM2.step (program tromino))
                  (scanVerticalCfg initial)
                  (some (scanVerticalCfg next)) 1 := by
                simpa [initial, next, activeData, List.replicate_succ]
                  using first
              have rest := induction .vertical horizontal (vertical + 1)
                outputReverse
              have whole := EvalsToInTime.trans (TM2.step (program tromino))
                1 (scanTime tromino .vertical horizontal (vertical + 1) tokens)
                (scanVerticalCfg initial) (scanVerticalCfg next)
                (some (reverseOutputCfg
                  (activeData [] 0 0
                    ((phaseExpand tromino .vertical horizontal (vertical + 1)
                      tokens).reverse ++ outputReverse) output))) first'
                (by simpa [phaseCfg, phaseData, phaseVertical, next] using rest)
              simpa [phaseCfg, phaseData, phaseVertical, phaseExpand,
                GadgetSparseAssignmentTokens.expandAux, scanTime, initial]
                using whole
          | fieldEnd =>
              let initial := activeData (.fieldEnd :: tokens)
                horizontal vertical outputReverse output
              let afterInput := activeData tokens horizontal vertical
                outputReverse output
              have first := oneStep
                (step_scanVertical_fieldEnd tromino initial tokens rfl)
              have cleared := clearToScan_evalsInTime tromino tokens horizontal
                vertical outputReverse output
              have throughClear := EvalsToInTime.trans
                (TM2.step (program tromino)) 1 (horizontal + vertical + 2)
                (scanVerticalCfg initial)
                (clearHorizontalCfg .scan afterInput)
                (some (scanHorizontalCfg
                  (activeData tokens 0 0 outputReverse output)))
                (by simpa [initial, afterInput, activeData] using first)
                (by simpa [afterInput] using cleared)
              have rest := induction .horizontal 0 0 outputReverse
              have whole := EvalsToInTime.trans (TM2.step (program tromino))
                (horizontal + vertical + 2 + 1)
                (scanTime tromino .horizontal 0 0 tokens)
                (scanVerticalCfg initial)
                (scanHorizontalCfg (activeData tokens 0 0 outputReverse output))
                (some (reverseOutputCfg
                  (activeData [] 0 0
                    ((phaseExpand tromino .horizontal 0 0 tokens).reverse ++
                      outputReverse) output))) throughClear
                (by simpa [phaseCfg, phaseData, phaseVertical] using rest)
              convert whole using 1
              · rfl
              · rfl
              · change scanTime tromino .horizontal 0 0 tokens +
                    (horizontal + vertical + 2 + 1) =
                  scanTime tromino .horizontal 0 0 tokens +
                    (horizontal + vertical + 2 + 1)
                rfl
          | cellType cellType =>
              let initial := activeData (.cellType cellType :: tokens)
                horizontal vertical outputReverse output
              let afterInput := activeData tokens horizontal vertical
                outputReverse output
              have first := oneStep
                (step_scanVertical_cellType tromino initial cellType tokens rfl)
              have finished := finishCell_evalsInTime tromino cellType
                (some (.inl (.cellType cellType))) tokens horizontal vertical
                outputReverse output
              have throughCell := EvalsToInTime.trans
                (TM2.step (program tromino)) 1
                (1 + pixelsTime horizontal vertical
                    (boundedPixels tromino cellType) +
                  (horizontal + vertical + 2))
                (scanVerticalCfg initial)
                (beginPixelsCfg cellType (some (.inl (.cellType cellType)))
                  afterInput)
                (some (scanHorizontalCfg
                  (activeData tokens 0 0
                    ((GadgetSparseAssignmentTokens.preparedNatAssignmentPixels
                        tromino horizontal vertical cellType).reverse ++
                      outputReverse) output)))
                (by simpa [initial, afterInput, activeData] using first)
                (by simpa [afterInput] using finished)
              have rest := induction .horizontal 0 0
                ((GadgetSparseAssignmentTokens.preparedNatAssignmentPixels
                  tromino horizontal vertical cellType).reverse ++ outputReverse)
              have whole := EvalsToInTime.trans (TM2.step (program tromino))
                (1 + pixelsTime horizontal vertical
                    (boundedPixels tromino cellType) +
                  (horizontal + vertical + 2) + 1)
                (scanTime tromino .horizontal 0 0 tokens)
                (scanVerticalCfg initial)
                (scanHorizontalCfg
                  (activeData tokens 0 0
                    ((GadgetSparseAssignmentTokens.preparedNatAssignmentPixels
                        tromino horizontal vertical cellType).reverse ++
                      outputReverse) output))
                (some (reverseOutputCfg
                  (activeData [] 0 0
                    ((phaseExpand tromino .horizontal 0 0 tokens).reverse ++
                      (GadgetSparseAssignmentTokens.preparedNatAssignmentPixels
                        tromino horizontal vertical cellType).reverse ++
                        outputReverse) output))) throughCell
                (by simpa [phaseCfg, phaseData, phaseVertical,
                    List.append_assoc] using rest)
              convert whole using 1
              · rfl
              · simp [phaseExpand, phaseVertical,
                  GadgetSparseAssignmentTokens.expandAux,
                  List.reverse_append, List.append_assoc]
              · change scanTime tromino .horizontal 0 0 tokens +
                    (1 + pixelsTime horizontal vertical
                        (boundedPixels tromino cellType) +
                      (horizontal + vertical + 2) + 1) =
                  scanTime tromino .horizontal 0 0 tokens +
                    (1 + pixelsTime horizontal vertical
                        (boundedPixels tromino cellType) +
                      (horizontal + vertical + 2) + 1)
                rfl

end GadgetSparseAssignmentTokenMachine
end
end LeanTrominoes
