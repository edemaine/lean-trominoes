/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenMachineSteps
import LeanTrominoes.FiniteBlockTransducer

/-! # Exact coordinate-copy executions for sparse assignment tokens -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseAssignmentTokenMachine

open Gadget

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

/-- Reverse-stack contribution of one prepared affine coordinate field. -/
def coordinateReverse (count : Nat) (offset : Fin 6) : List OutputToken :=
  [.fieldEnd, .localOffset offset] ++
    List.replicate count .coordinateUnit

@[simp] theorem coordinateReverse_zero (offset : Fin 6) :
    coordinateReverse 0 offset = [.fieldEnd, .localOffset offset] := by
  simp [coordinateReverse]

theorem coordinateReverse_succ (count : Nat) (offset : Fin 6)
    (tail : List OutputToken) :
    coordinateReverse count offset ++ .coordinateUnit :: tail =
      coordinateReverse (count + 1) offset ++ tail := by
  simp only [coordinateReverse, List.append_assoc, List.replicate_succ',
    List.singleton_append]

/-- Drain the horizontal counter, recording a reversed copy on scratch and
in the reverse output. -/
def copyHorizontal_evalsInTime (tromino : Tromino)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (word : List Unit) (data : TapeData)
    (horizontalEq : data.horizontal = word) :
    EvalsToInTime (TM2.step (program tromino))
      (copyHorizontalCfg cellType index pixel data)
      (some (restoreHorizontalCfg cellType index pixel
        { data with
          horizontal := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            coordinateReverse word.length pixel.1 ++ data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_copyHorizontal_nil tromino data cellType index pixel horizontalEq)
      convert step using 1 <;> simp [coordinateReverse]
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with
          horizontal := word
          scratch := () :: data.scratch
          outputReverse := .coordinateUnit :: data.outputReverse }
      have first := oneStep
        (step_copyHorizontal_cons tromino data cellType index pixel word
          horizontalEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step (program tromino))
        1 (word.length + 1)
        (copyHorizontalCfg cellType index pixel data)
        (copyHorizontalCfg cellType index pixel nextData)
        (some (restoreHorizontalCfg cellType index pixel
          { nextData with
            horizontal := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse := coordinateReverse word.length pixel.1 ++
              nextData.outputReverse })) first rest
      convert composed using 1
      · simp only [nextData, List.reverse_cons, List.append_assoc,
          List.singleton_append, List.length_cons]
        rw [coordinateReverse_succ]
      · simp

/-- Restore a drained horizontal counter and continue with the vertical
copy. -/
def restoreHorizontal_evalsInTime (tromino : Tromino)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (word : List Unit) (data : TapeData)
    (scratchEq : data.scratch = word) :
    EvalsToInTime (TM2.step (program tromino))
      (restoreHorizontalCfg cellType index pixel data)
      (some (copyVerticalCfg cellType index pixel
        { data with
          horizontal := word.reverse ++ data.horizontal
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreHorizontal_nil tromino data cellType index pixel scratchEq)
      convert step using 1 <;> simp
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with
          horizontal := () :: data.horizontal
          scratch := word }
      have first := oneStep
        (step_restoreHorizontal_cons tromino data cellType index pixel word
          scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step (program tromino))
        1 (word.length + 1)
        (restoreHorizontalCfg cellType index pixel data)
        (restoreHorizontalCfg cellType index pixel nextData)
        (some (copyVerticalCfg cellType index pixel
          { nextData with
            horizontal := word.reverse ++ nextData.horizontal
            scratch := [] })) first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- Copy and restore one entire horizontal coordinate. -/
def copyHorizontalThrough_evalsInTime (tromino : Tromino)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (word : List Unit) (data : TapeData)
    (horizontalEq : data.horizontal = word)
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program tromino))
      (copyHorizontalCfg cellType index pixel data)
      (some (copyVerticalCfg cellType index pixel
        { data with
          horizontal := word
          scratch := []
          outputReverse :=
            coordinateReverse word.length pixel.1 ++ data.outputReverse }))
      (2 * word.length + 2) := by
  have copied := copyHorizontal_evalsInTime tromino cellType index pixel
    word data horizontalEq
  let copiedData : TapeData :=
    { data with
      horizontal := []
      scratch := word.reverse ++ data.scratch
      outputReverse :=
        coordinateReverse word.length pixel.1 ++ data.outputReverse }
  have restored := restoreHorizontal_evalsInTime tromino cellType index pixel
    word.reverse copiedData (by simp [copiedData, scratchEq])
  have composed := EvalsToInTime.trans (TM2.step (program tromino))
    (word.length + 1) (word.reverse.length + 1)
    (copyHorizontalCfg cellType index pixel data)
    (restoreHorizontalCfg cellType index pixel copiedData)
    (some (copyVerticalCfg cellType index pixel
      { copiedData with
        horizontal := word.reverse.reverse ++ copiedData.horizontal
        scratch := [] })) copied (by simpa [copiedData] using restored)
  convert composed using 1
  · simp [copiedData]
  · simp
    omega

/-- Configuration reached after restoring the vertical coordinate. -/
def afterPixelCfg (cellType : OrthogonalCellType) (index : PixelIndex)
    (data : TapeData) : TM2.Cfg Alphabet Label State :=
  match nextPixelIndex index with
  | some next => pixelStartCfg cellType next data
  | none => clearHorizontalCfg .scan data

/-- Drain the vertical counter into scratch and the reverse output. -/
def copyVertical_evalsInTime (tromino : Tromino)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (word : List Unit) (data : TapeData)
    (verticalEq : data.vertical = word) :
    EvalsToInTime (TM2.step (program tromino))
      (copyVerticalCfg cellType index pixel data)
      (some (restoreVerticalCfg cellType index pixel
        { data with
          vertical := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            coordinateReverse word.length pixel.2 ++ data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_copyVertical_nil tromino data cellType index pixel verticalEq)
      convert step using 1 <;> simp [coordinateReverse]
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with
          vertical := word
          scratch := () :: data.scratch
          outputReverse := .coordinateUnit :: data.outputReverse }
      have first := oneStep
        (step_copyVertical_cons tromino data cellType index pixel word
          verticalEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step (program tromino))
        1 (word.length + 1)
        (copyVerticalCfg cellType index pixel data)
        (copyVerticalCfg cellType index pixel nextData)
        (some (restoreVerticalCfg cellType index pixel
          { nextData with
            vertical := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse := coordinateReverse word.length pixel.2 ++
              nextData.outputReverse })) first rest
      convert composed using 1
      · simp only [nextData, List.reverse_cons, List.append_assoc,
          List.singleton_append, List.length_cons]
        rw [coordinateReverse_succ]
      · simp

/-- Restore a drained vertical counter and advance the finite pixel cursor. -/
def restoreVertical_evalsInTime (tromino : Tromino)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (word : List Unit) (data : TapeData)
    (scratchEq : data.scratch = word) :
    EvalsToInTime (TM2.step (program tromino))
      (restoreVerticalCfg cellType index pixel data)
      (some (afterPixelCfg cellType index
        { data with
          vertical := word.reverse ++ data.vertical
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      cases nextEq : nextPixelIndex index with
      | none =>
          have step := oneStep
            (step_restoreVertical_nil_none tromino data cellType index pixel
              scratchEq nextEq)
          convert step using 1 <;> simp [afterPixelCfg, nextEq]
      | some next =>
          have step := oneStep
            (step_restoreVertical_nil_some tromino data cellType index next
              pixel scratchEq nextEq)
          convert step using 1 <;> simp [afterPixelCfg, nextEq]
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with
          vertical := () :: data.vertical
          scratch := word }
      have first := oneStep
        (step_restoreVertical_cons tromino data cellType index pixel word
          scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step (program tromino))
        1 (word.length + 1)
        (restoreVerticalCfg cellType index pixel data)
        (restoreVerticalCfg cellType index pixel nextData)
        (some (afterPixelCfg cellType index
          { nextData with
            vertical := word.reverse ++ nextData.vertical
            scratch := [] })) first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- Copy and restore one entire vertical coordinate. -/
def copyVerticalThrough_evalsInTime (tromino : Tromino)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (word : List Unit) (data : TapeData)
    (verticalEq : data.vertical = word)
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program tromino))
      (copyVerticalCfg cellType index pixel data)
      (some (afterPixelCfg cellType index
        { data with
          vertical := word
          scratch := []
          outputReverse :=
            coordinateReverse word.length pixel.2 ++ data.outputReverse }))
      (2 * word.length + 2) := by
  have copied := copyVertical_evalsInTime tromino cellType index pixel
    word data verticalEq
  let copiedData : TapeData :=
    { data with
      vertical := []
      scratch := word.reverse ++ data.scratch
      outputReverse :=
        coordinateReverse word.length pixel.2 ++ data.outputReverse }
  have restored := restoreVertical_evalsInTime tromino cellType index pixel
    word.reverse copiedData (by simp [copiedData, scratchEq])
  have composed := EvalsToInTime.trans (TM2.step (program tromino))
    (word.length + 1) (word.reverse.length + 1)
    (copyVerticalCfg cellType index pixel data)
    (restoreVerticalCfg cellType index pixel copiedData)
    (some (afterPixelCfg cellType index
      { copiedData with
        vertical := word.reverse.reverse ++ copiedData.vertical
        scratch := [] })) copied (by simpa [copiedData] using restored)
  convert composed using 1
  · simp [copiedData]
  · simp
    omega

end GadgetSparseAssignmentTokenMachine
end
end LeanTrominoes
