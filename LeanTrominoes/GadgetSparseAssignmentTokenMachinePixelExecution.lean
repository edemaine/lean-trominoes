/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenPixels

/-! # Exact finite-pixel cursor execution for sparse assignments -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseAssignmentTokenMachine

open Gadget

/-- Canonical live tapes while expanding one assignment record. -/
def activeData (input : List InputToken) (horizontal vertical : Nat)
    (outputReverse output : List OutputToken) : TapeData :=
  ⟨input, List.replicate horizontal (), List.replicate vertical (), [],
    outputReverse, output⟩

theorem coordinateReverse_eq_coordinateField_reverse (count : Nat)
    (offset : Fin 6) :
    coordinateReverse count offset =
      (GadgetPixelFiniteTokens.coordinateField count offset).reverse := by
  simp [coordinateReverse, GadgetPixelFiniteTokens.coordinateField,
    List.reverse_append]

theorem pixelBlock_reverse (horizontal vertical : Nat)
    (pixel : LocalPixel) :
    (GadgetPixelFiniteTokens.pixelBlock horizontal vertical pixel).reverse =
      coordinateReverse vertical pixel.2 ++
        coordinateReverse horizontal pixel.1 ++ [.cellMarker] := by
  simp only [GadgetPixelFiniteTokens.pixelBlock, List.reverse_cons,
    List.reverse_append]
  rw [← coordinateReverse_eq_coordinateField_reverse,
    ← coordinateReverse_eq_coordinateField_reverse]

/-- One occupied cursor emits one exact prepared pixel block and advances. -/
def emitPixel_evalsInTime (tromino : Tromino)
    (cellType : OrthogonalCellType) (index next : PixelIndex)
    (pixel : LocalPixel) (input : List InputToken)
    (horizontal vertical : Nat) (outputReverse output : List OutputToken)
    (pixelEq : pixelAt? tromino cellType index = some pixel)
    (nextEq : nextPixelIndex index = some next) :
    EvalsToInTime (TM2.step (program tromino))
      (pixelStartCfg cellType index
        (activeData input horizontal vertical outputReverse output))
      (some (pixelStartCfg cellType next
        (activeData input horizontal vertical
          ((GadgetPixelFiniteTokens.pixelBlock horizontal vertical pixel).reverse ++
            outputReverse) output)))
      (pixelTime horizontal vertical) := by
  let initial := activeData input horizontal vertical outputReverse output
  let marked : TapeData :=
    activeData input horizontal vertical (.cellMarker :: outputReverse) output
  have first := oneStep
    (step_pixelStart_some tromino initial cellType index pixel pixelEq)
  have first' : EvalsToInTime (TM2.step (program tromino))
      (pixelStartCfg cellType index initial)
      (some (copyHorizontalCfg cellType index pixel marked)) 1 := by
    simpa [initial, marked, activeData] using first
  let afterHorizontal : TapeData :=
    activeData input horizontal vertical
      (coordinateReverse horizontal pixel.1 ++ .cellMarker :: outputReverse)
      output
  have horizontalRun := copyHorizontalThrough_evalsInTime tromino
    cellType index pixel (List.replicate horizontal ()) marked rfl rfl
  have horizontalRun' : EvalsToInTime (TM2.step (program tromino))
      (copyHorizontalCfg cellType index pixel marked)
      (some (copyVerticalCfg cellType index pixel afterHorizontal))
      (2 * horizontal + 2) := by
    simpa [marked, afterHorizontal, activeData] using horizontalRun
  have throughHorizontal := EvalsToInTime.trans (TM2.step (program tromino))
    1 (2 * horizontal + 2)
    (pixelStartCfg cellType index initial)
    (copyHorizontalCfg cellType index pixel marked)
    (some (copyVerticalCfg cellType index pixel afterHorizontal))
    first' horizontalRun'
  let afterVertical : TapeData :=
    activeData input horizontal vertical
      (coordinateReverse vertical pixel.2 ++
        coordinateReverse horizontal pixel.1 ++
          .cellMarker :: outputReverse) output
  have verticalRun := copyVerticalThrough_evalsInTime tromino
    cellType index pixel (List.replicate vertical ()) afterHorizontal rfl rfl
  have verticalRun' : EvalsToInTime (TM2.step (program tromino))
      (copyVerticalCfg cellType index pixel afterHorizontal)
      (some (pixelStartCfg cellType next afterVertical))
      (2 * vertical + 2) := by
    simpa [afterHorizontal, afterVertical, activeData, afterPixelCfg,
      nextEq, List.append_assoc] using verticalRun
  have whole := EvalsToInTime.trans (TM2.step (program tromino))
    (2 * horizontal + 2 + 1) (2 * vertical + 2)
    (pixelStartCfg cellType index initial)
    (copyVerticalCfg cellType index pixel afterHorizontal)
    (some (pixelStartCfg cellType next afterVertical))
    throughHorizontal verticalRun'
  convert whole using 1
  · simp [afterVertical, activeData, pixelBlock_reverse,
      List.append_assoc]
  · simp [pixelTime]
    omega

theorem pixelAt?_eq_none_of_drop_eq_nil (tromino : Tromino)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (dropEq : (boundedPixels tromino cellType).drop index.val = []) :
    pixelAt? tromino cellType index = none := by
  rw [pixelAt?_eq]
  have equality := congrArg (fun pixels : List LocalPixel => pixels[0]?) dropEq
  simpa [List.getElem?_drop] using equality

theorem pixelAt?_eq_some_of_drop_eq_cons (tromino : Tromino)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (pixels : List LocalPixel)
    (dropEq :
      (boundedPixels tromino cellType).drop index.val = pixel :: pixels) :
    pixelAt? tromino cellType index = some pixel := by
  rw [pixelAt?_eq]
  have equality := congrArg (fun values : List LocalPixel => values[0]?) dropEq
  simpa [List.getElem?_drop] using equality

/-- A nonempty cursor suffix has a successor inside the reserved 37-state
range, and dropping at that successor gives exactly its tail. -/
theorem nextPixelIndex_of_drop_eq_cons (tromino : Tromino)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (pixels : List LocalPixel)
    (dropEq :
      (boundedPixels tromino cellType).drop index.val = pixel :: pixels) :
    ∃ next : PixelIndex,
      nextPixelIndex index = some next ∧
        (boundedPixels tromino cellType).drop next.val = pixels := by
  have suffixPositive :
      0 < ((boundedPixels tromino cellType).drop index.val).length := by
    rw [dropEq]
    simp
  rw [List.length_drop] at suffixPositive
  have lengthBound := boundedPixels_length_le tromino cellType
  have nextInRange : index.val + 1 < 37 := by omega
  let next : PixelIndex := ⟨index.val + 1, nextInRange⟩
  refine ⟨next, ?_, ?_⟩
  · simp [nextPixelIndex, next, nextInRange]
  · have tailDrop := congrArg (List.drop 1) dropEq
    simpa [List.drop_drop] using tailDrop

/-- Execute an arbitrary suffix of the bounded pixel list, ending at its
first empty cursor. -/
def pixels_evalsInTime (tromino : Tromino)
    (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixels : List LocalPixel) (input : List InputToken)
    (horizontal vertical : Nat) (outputReverse output : List OutputToken)
    (dropEq :
      (boundedPixels tromino cellType).drop index.val = pixels) :
    EvalsToInTime (TM2.step (program tromino))
      (pixelStartCfg cellType index
        (activeData input horizontal vertical outputReverse output))
      (some (clearHorizontalCfg .scan
        (activeData input horizontal vertical
          ((preparedPixels horizontal vertical pixels).reverse ++ outputReverse)
          output)))
      (pixelsTime horizontal vertical pixels) := by
  induction pixels generalizing index outputReverse with
  | nil =>
      have pixelEq := pixelAt?_eq_none_of_drop_eq_nil
        tromino cellType index dropEq
      have step := oneStep (step_pixelStart_none tromino
        (activeData input horizontal vertical outputReverse output)
        cellType index pixelEq)
      convert step using 1 <;> simp [preparedPixels, pixelsTime]
  | cons pixel pixels induction =>
      have pixelEq := pixelAt?_eq_some_of_drop_eq_cons
        tromino cellType index pixel pixels dropEq
      have suffixPositive :
          0 < ((boundedPixels tromino cellType).drop index.val).length := by
        rw [dropEq]
        simp
      rw [List.length_drop] at suffixPositive
      have lengthBound := boundedPixels_length_le tromino cellType
      have nextInRange : index.val + 1 < 37 := by omega
      let next : PixelIndex := ⟨index.val + 1, nextInRange⟩
      have nextEq : nextPixelIndex index = some next := by
        simp [nextPixelIndex, next, nextInRange]
      have nextDropEq :
          (boundedPixels tromino cellType).drop next.val = pixels := by
        have tailDrop := congrArg (List.drop 1) dropEq
        simpa [next, List.drop_drop] using tailDrop
      have first := emitPixel_evalsInTime tromino cellType index next pixel
        input horizontal vertical outputReverse output pixelEq nextEq
      have rest := induction next
        ((GadgetPixelFiniteTokens.pixelBlock horizontal vertical pixel).reverse ++
          outputReverse) nextDropEq
      have composed := EvalsToInTime.trans (TM2.step (program tromino))
        (pixelTime horizontal vertical)
        (pixelsTime horizontal vertical pixels)
        (pixelStartCfg cellType index
          (activeData input horizontal vertical outputReverse output))
        (pixelStartCfg cellType next
          (activeData input horizontal vertical
            ((GadgetPixelFiniteTokens.pixelBlock horizontal vertical pixel).reverse ++
              outputReverse) output))
        (some (clearHorizontalCfg .scan
          (activeData input horizontal vertical
            ((preparedPixels horizontal vertical pixels).reverse ++
              (GadgetPixelFiniteTokens.pixelBlock horizontal vertical pixel).reverse ++
                outputReverse) output))) first
        (by simpa [List.append_assoc] using rest)
      convert composed using 1
      · simp [preparedPixels, List.reverse_append, List.append_assoc]
      · simp only [pixelsTime]
        omega

/-- Execute the complete fixed local mask from cursor zero. -/
def completePixels_evalsInTime (tromino : Tromino)
    (cellType : OrthogonalCellType) (input : List InputToken)
    (horizontal vertical : Nat) (outputReverse output : List OutputToken) :
    EvalsToInTime (TM2.step (program tromino))
      (pixelStartCfg cellType firstPixelIndex
        (activeData input horizontal vertical outputReverse output))
      (some (clearHorizontalCfg .scan
        (activeData input horizontal vertical
          ((GadgetSparseAssignmentTokens.preparedNatAssignmentPixels tromino
              horizontal vertical cellType).reverse ++ outputReverse) output)))
      (pixelsTime horizontal vertical (boundedPixels tromino cellType)) := by
  have run := pixels_evalsInTime tromino cellType firstPixelIndex
    (boundedPixels tromino cellType) input horizontal vertical outputReverse
    output (by simp [firstPixelIndex])
  simpa [preparedPixels_boundedPixels] using run

end GadgetSparseAssignmentTokenMachine
end
end LeanTrominoes
