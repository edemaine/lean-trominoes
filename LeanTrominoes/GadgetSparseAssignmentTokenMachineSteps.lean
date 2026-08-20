/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenMachine

/-! # One-step equations for sparse assignment-token expansion -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseAssignmentTokenMachine

open Gadget

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List InputToken) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_horizontal (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.horizontal value =
      tapes { data with horizontal := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_vertical (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.vertical value =
      tapes { data with vertical := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_scratch (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.scratch value =
      tapes { data with scratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse (data : TapeData)
    (value : List OutputToken) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output (data : TapeData)
    (value : List OutputToken) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_scanHorizontal_nil (tromino : Tromino) (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step (program tromino) (scanHorizontalCfg data) =
      some (clearHorizontalCfg .reverseOutput
        { data with input := [] }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanHorizontalCfg, clearHorizontalCfg, cfg, tapes]

theorem step_scanHorizontal_coordinateUnit (tromino : Tromino)
    (data : TapeData) (tail : List InputToken)
    (inputEq : data.input = .coordinateUnit :: tail) :
    TM2.step (program tromino) (scanHorizontalCfg data) =
      some (scanHorizontalCfg
        { data with
          input := tail
          horizontal := () :: data.horizontal }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change input = .coordinateUnit :: tail at inputEq
  subst input
  simp [TM2.step, program, scanHorizontalCfg, cfg, tapes,
    isCoordinateUnitState]

theorem step_scanHorizontal_fieldEnd (tromino : Tromino)
    (data : TapeData) (tail : List InputToken)
    (inputEq : data.input = .fieldEnd :: tail) :
    TM2.step (program tromino) (scanHorizontalCfg data) =
      some (scanVerticalCfg { data with input := tail }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change input = .fieldEnd :: tail at inputEq
  subst input
  simp [TM2.step, program, scanHorizontalCfg, scanVerticalCfg, cfg, tapes,
    isCoordinateUnitState, isFieldEndState]

theorem step_scanHorizontal_cellType (tromino : Tromino)
    (data : TapeData) (cellType : OrthogonalCellType)
    (tail : List InputToken)
    (inputEq : data.input = .cellType cellType :: tail) :
    TM2.step (program tromino) (scanHorizontalCfg data) =
      some (clearHorizontalCfg .scan { data with input := tail }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change input = .cellType cellType :: tail at inputEq
  subst input
  simp [TM2.step, program, scanHorizontalCfg, clearHorizontalCfg, cfg, tapes,
    isCoordinateUnitState, isFieldEndState]

theorem step_scanVertical_nil (tromino : Tromino) (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step (program tromino) (scanVerticalCfg data) =
      some (clearHorizontalCfg .reverseOutput
        { data with input := [] }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanVerticalCfg, clearHorizontalCfg, cfg, tapes]

theorem step_scanVertical_coordinateUnit (tromino : Tromino)
    (data : TapeData) (tail : List InputToken)
    (inputEq : data.input = .coordinateUnit :: tail) :
    TM2.step (program tromino) (scanVerticalCfg data) =
      some (scanVerticalCfg
        { data with
          input := tail
          vertical := () :: data.vertical }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change input = .coordinateUnit :: tail at inputEq
  subst input
  simp [TM2.step, program, scanVerticalCfg, cfg, tapes,
    isCoordinateUnitState]

theorem step_scanVertical_fieldEnd (tromino : Tromino)
    (data : TapeData) (tail : List InputToken)
    (inputEq : data.input = .fieldEnd :: tail) :
    TM2.step (program tromino) (scanVerticalCfg data) =
      some (clearHorizontalCfg .scan { data with input := tail }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change input = .fieldEnd :: tail at inputEq
  subst input
  simp [TM2.step, program, scanVerticalCfg, clearHorizontalCfg, cfg, tapes,
    isCoordinateUnitState, isFieldEndState]

theorem step_scanVertical_cellType (tromino : Tromino)
    (data : TapeData) (cellType : OrthogonalCellType)
    (tail : List InputToken)
    (inputEq : data.input = .cellType cellType :: tail) :
    TM2.step (program tromino) (scanVerticalCfg data) =
      some (beginPixelsCfg cellType
        (some (.inl (.cellType cellType))) { data with input := tail }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change input = .cellType cellType :: tail at inputEq
  subst input
  simp [TM2.step, program, scanVerticalCfg, beginPixelsCfg, cfg, tapes,
    isCoordinateUnitState, isFieldEndState, cellTypeFromState]

theorem step_beginPixels (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (state : State) :
    TM2.step (program tromino) (beginPixelsCfg cellType state data) =
      some (pixelStartCfg cellType firstPixelIndex data) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  simp [TM2.step, program, beginPixelsCfg, pixelStartCfg, cfg]

theorem step_pixelStart_none (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixelEq : pixelAt? tromino cellType index = none) :
    TM2.step (program tromino) (pixelStartCfg cellType index data) =
      some (clearHorizontalCfg .scan data) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  simp [TM2.step, program, pixelStartCfg, clearHorizontalCfg, cfg,
    pixelEq]

theorem step_pixelStart_some (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (pixelEq : pixelAt? tromino cellType index = some pixel) :
    TM2.step (program tromino) (pixelStartCfg cellType index data) =
      some (copyHorizontalCfg cellType index pixel
        { data with outputReverse := .cellMarker :: data.outputReverse }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  simp [TM2.step, program, pixelStartCfg, copyHorizontalCfg, cfg, tapes,
    pixelEq]

theorem step_copyHorizontal_nil (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (horizontalEq : data.horizontal = []) :
    TM2.step (program tromino)
        (copyHorizontalCfg cellType index pixel data) =
      some (restoreHorizontalCfg cellType index pixel
        { data with
          horizontal := []
          outputReverse :=
            .fieldEnd :: .localOffset pixel.1 :: data.outputReverse }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change horizontal = [] at horizontalEq
  subst horizontal
  simp [TM2.step, program, copyHorizontalCfg, restoreHorizontalCfg, cfg,
    tapes]

theorem step_copyHorizontal_cons (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (tail : List Unit)
    (horizontalEq : data.horizontal = () :: tail) :
    TM2.step (program tromino)
        (copyHorizontalCfg cellType index pixel data) =
      some (copyHorizontalCfg cellType index pixel
        { data with
          horizontal := tail
          scratch := () :: data.scratch
          outputReverse := .coordinateUnit :: data.outputReverse }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change horizontal = () :: tail at horizontalEq
  subst horizontal
  simp [TM2.step, program, copyHorizontalCfg, cfg, tapes]

theorem step_restoreHorizontal_nil (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (scratchEq : data.scratch = []) :
    TM2.step (program tromino)
        (restoreHorizontalCfg cellType index pixel data) =
      some (copyVerticalCfg cellType index pixel
        { data with scratch := [] }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, restoreHorizontalCfg, copyVerticalCfg, cfg, tapes]

theorem step_restoreHorizontal_cons (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (tail : List Unit)
    (scratchEq : data.scratch = () :: tail) :
    TM2.step (program tromino)
        (restoreHorizontalCfg cellType index pixel data) =
      some (restoreHorizontalCfg cellType index pixel
        { data with
          horizontal := () :: data.horizontal
          scratch := tail }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restoreHorizontalCfg, cfg, tapes]

theorem step_copyVertical_nil (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (verticalEq : data.vertical = []) :
    TM2.step (program tromino)
        (copyVerticalCfg cellType index pixel data) =
      some (restoreVerticalCfg cellType index pixel
        { data with
          vertical := []
          outputReverse :=
            .fieldEnd :: .localOffset pixel.2 :: data.outputReverse }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change vertical = [] at verticalEq
  subst vertical
  simp [TM2.step, program, copyVerticalCfg, restoreVerticalCfg, cfg, tapes]

theorem step_copyVertical_cons (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (tail : List Unit)
    (verticalEq : data.vertical = () :: tail) :
    TM2.step (program tromino)
        (copyVerticalCfg cellType index pixel data) =
      some (copyVerticalCfg cellType index pixel
        { data with
          vertical := tail
          scratch := () :: data.scratch
          outputReverse := .coordinateUnit :: data.outputReverse }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change vertical = () :: tail at verticalEq
  subst vertical
  simp [TM2.step, program, copyVerticalCfg, cfg, tapes]

theorem step_restoreVertical_nil_some (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index next : PixelIndex)
    (pixel : LocalPixel) (scratchEq : data.scratch = [])
    (nextEq : nextPixelIndex index = some next) :
    TM2.step (program tromino)
        (restoreVerticalCfg cellType index pixel data) =
      some (pixelStartCfg cellType next { data with scratch := [] }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, restoreVerticalCfg, pixelStartCfg, cfg, tapes,
    nextEq]

theorem step_restoreVertical_nil_none (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (scratchEq : data.scratch = [])
    (nextEq : nextPixelIndex index = none) :
    TM2.step (program tromino)
        (restoreVerticalCfg cellType index pixel data) =
      some (clearHorizontalCfg .scan { data with scratch := [] }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, restoreVerticalCfg, clearHorizontalCfg, cfg, tapes,
    nextEq]

theorem step_restoreVertical_cons (tromino : Tromino) (data : TapeData)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (tail : List Unit)
    (scratchEq : data.scratch = () :: tail) :
    TM2.step (program tromino)
        (restoreVerticalCfg cellType index pixel data) =
      some (restoreVerticalCfg cellType index pixel
        { data with
          vertical := () :: data.vertical
          scratch := tail }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restoreVerticalCfg, cfg, tapes]

theorem step_clearHorizontal_nil (tromino : Tromino) (data : TapeData)
    (target : ResetTarget) (horizontalEq : data.horizontal = []) :
    TM2.step (program tromino) (clearHorizontalCfg target data) =
      some (clearVerticalCfg target { data with horizontal := [] }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change horizontal = [] at horizontalEq
  subst horizontal
  cases target <;>
    simp [TM2.step, program, clearHorizontalCfg, clearVerticalCfg, cfg, tapes]

theorem step_clearHorizontal_cons (tromino : Tromino) (data : TapeData)
    (target : ResetTarget) (tail : List Unit)
    (horizontalEq : data.horizontal = () :: tail) :
    TM2.step (program tromino) (clearHorizontalCfg target data) =
      some (clearHorizontalCfg target { data with horizontal := tail }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change horizontal = () :: tail at horizontalEq
  subst horizontal
  cases target <;>
    simp [TM2.step, program, clearHorizontalCfg, cfg, tapes]

theorem step_clearVertical_nil (tromino : Tromino) (data : TapeData)
    (target : ResetTarget) (verticalEq : data.vertical = []) :
    TM2.step (program tromino) (clearVerticalCfg target data) =
      some (cfg (afterClear target) none { data with vertical := [] }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change vertical = [] at verticalEq
  subst vertical
  cases target with
  | scan =>
      simp [TM2.step, program, clearVerticalCfg, afterClear, cfg, tapes]
  | reverseOutput =>
      simp [TM2.step, program, clearVerticalCfg, afterClear, cfg, tapes]

theorem step_clearVertical_cons (tromino : Tromino) (data : TapeData)
    (target : ResetTarget) (tail : List Unit)
    (verticalEq : data.vertical = () :: tail) :
    TM2.step (program tromino) (clearVerticalCfg target data) =
      some (clearVerticalCfg target { data with vertical := tail }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change vertical = () :: tail at verticalEq
  subst vertical
  cases target <;>
    simp [TM2.step, program, clearVerticalCfg, cfg, tapes]

theorem step_reverseOutput_nil (tromino : Tromino) (data : TapeData)
    (outputReverseEq : data.outputReverse = []) :
    TM2.step (program tromino) (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change outputReverse = [] at outputReverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg, cfg, tapes]

theorem step_reverseOutput_cons (tromino : Tromino) (data : TapeData)
    (token : OutputToken) (tail : List OutputToken)
    (outputReverseEq : data.outputReverse = token :: tail) :
    TM2.step (program tromino) (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := token :: data.output }) := by
  rcases data with
    ⟨input, horizontal, vertical, scratch, outputReverse, output⟩
  change outputReverse = token :: tail at outputReverseEq
  subst outputReverse
  cases token <;>
    simp [TM2.step, program, reverseOutputCfg, cfg, tapes, outputFromState]

end GadgetSparseAssignmentTokenMachine
end
end LeanTrominoes
