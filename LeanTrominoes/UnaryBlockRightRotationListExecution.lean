/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationBlockExecution
import LeanTrominoes.UnaryBlockRightRotationFieldScanExecution
import LeanTrominoes.UnaryBlockRightRotationInput

/-! # Executing aligned lists of unary block right rotations -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def blocksOutputReverse : List Nat → List Nat → List UnarySymbol
  | groupSize :: groupSizes, blockStart :: blockStarts =>
      blocksOutputReverse groupSizes blockStarts ++
        blockOutputReverse blockStart groupSize
  | _, _ => []

def fieldsTime : List Nat → List Nat → Nat
  | groupSize :: groupSizes, blockStart :: blockStarts =>
      fieldsTime groupSizes blockStarts +
        (blockTime blockStart groupSize +
          ((2 * blockStart + 1) + (2 * groupSize + 1)))
  | _, _ => 0

def fields_evalsInTime {groupSizes blockStarts : List Nat}
    (valid : Valid groupSizes blockStarts) (data : TapeData)
    (sizesEq : data.sizes =
      UnaryFieldEncoderMachine.unaryFields groupSizes)
    (startsEq : data.starts =
      UnaryFieldEncoderMachine.unaryFields blockStarts)
    (groupEq : data.group = [])
    (remainingEq : data.groupRemaining = [])
    (startEq : data.start = [])
    (startRestoreEq : data.startRestore = [])
    (positionEq : data.position = [])
    (positionRestoreEq : data.positionRestore = []) :
    EvalsToInTime machine.step (scanSizeFieldCfg data)
      (some (scanSizeFieldCfg
        { data with
          sizes := []
          starts := []
          group := []
          groupRemaining := []
          start := []
          startRestore := []
          position := []
          positionRestore := []
          outputReverse :=
            blocksOutputReverse groupSizes blockStarts ++
              data.outputReverse }))
      (fieldsTime groupSizes blockStarts) := by
  induction valid generalizing data with
  | nil =>
      rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
        group, groupRemaining, start, startRestore, position,
        positionRestore, outputReverse, output⟩
      change sizes = UnaryFieldEncoderMachine.unaryFields [] at sizesEq
      change starts = UnaryFieldEncoderMachine.unaryFields [] at startsEq
      simp only [UnaryFieldEncoderMachine.unaryFields_nil] at sizesEq startsEq
      change group = [] at groupEq
      change groupRemaining = [] at remainingEq
      change start = [] at startEq
      change startRestore = [] at startRestoreEq
      change position = [] at positionEq
      change positionRestore = [] at positionRestoreEq
      subst sizes
      subst starts
      subst group
      subst groupRemaining
      subst start
      subst startRestore
      subst position
      subst positionRestore
      have zero := EvalsToInTime.refl machine.step
        (scanSizeFieldCfg
          ⟨input, sizesReverse, [], startsReverse, [], [], [], [], [],
            [], [], outputReverse, output⟩)
      simpa [fieldsTime, blocksOutputReverse] using zero
  | @cons groupSize blockStart groupSizes blockStarts valid induction =>
      let sizesRemaining : List UnarySymbol :=
        UnaryFieldEncoderMachine.unaryFields groupSizes
      let startsRemaining : List UnarySymbol :=
        UnaryFieldEncoderMachine.unaryFields blockStarts
      let afterSize : TapeData :=
        { data with
          sizes := sizesRemaining
          group := List.replicate groupSize () }
      have sizeFieldEq : data.sizes =
          UnaryFieldEncoderMachine.unaryField groupSize ++
            sizesRemaining := by
        simpa [sizesRemaining,
          UnaryFieldEncoderMachine.unaryFields_cons] using sizesEq
      have sizeRun := scanSizeField_evalsInTime
        groupSize sizesRemaining data sizeFieldEq
      have sizeRun' : EvalsToInTime machine.step
          (scanSizeFieldCfg data) (some (scanStartFieldCfg afterSize))
          (2 * groupSize + 1) := by
        simpa [afterSize, groupEq] using sizeRun
      let afterStart : TapeData :=
        { afterSize with
          starts := startsRemaining
          start := List.replicate blockStart () }
      have startFieldEq : afterSize.starts =
          UnaryFieldEncoderMachine.unaryField blockStart ++
            startsRemaining := by
        simpa [afterSize, startsRemaining,
          UnaryFieldEncoderMachine.unaryFields_cons] using startsEq
      have startRun := scanStartField_evalsInTime
        blockStart startsRemaining afterSize startFieldEq
      have startRun' : EvalsToInTime machine.step
          (scanStartFieldCfg afterSize) (some (beginGroupCfg afterStart))
          (2 * blockStart + 1) := by
        simpa [afterStart, afterSize, startEq] using startRun
      let afterBlock : TapeData :=
        { afterStart with
          group := []
          groupRemaining := []
          start := []
          startRestore := []
          position := []
          positionRestore := []
          outputReverse := blockOutputReverse blockStart groupSize ++
            data.outputReverse }
      have blockRun := block_evalsInTime
        blockStart groupSize afterStart rfl
          (by simpa [afterStart, afterSize] using remainingEq)
          rfl
          (by simpa [afterStart, afterSize] using startRestoreEq)
          (by simpa [afterStart, afterSize] using positionEq)
          (by simpa [afterStart, afterSize] using positionRestoreEq)
      have blockRun' : EvalsToInTime machine.step
          (beginGroupCfg afterStart) (some (scanSizeFieldCfg afterBlock))
          (blockTime blockStart groupSize) := by
        simpa [afterBlock, afterStart, afterSize] using blockRun
      have restRun := induction afterBlock rfl rfl rfl rfl rfl rfl rfl rfl
      have throughStart := EvalsToInTime.trans machine.step
        (2 * groupSize + 1) (2 * blockStart + 1)
        _ _ _ sizeRun' startRun'
      have throughBlock := EvalsToInTime.trans machine.step
        ((2 * blockStart + 1) + (2 * groupSize + 1))
        (blockTime blockStart groupSize)
        _ _ _ throughStart blockRun'
      have whole := EvalsToInTime.trans machine.step
        (blockTime blockStart groupSize +
          ((2 * blockStart + 1) + (2 * groupSize + 1)))
        (fieldsTime groupSizes blockStarts)
        _ _ _ throughBlock restRun
      simpa [afterBlock, afterStart, afterSize, fieldsTime,
        blocksOutputReverse, List.append_assoc] using whole

end LeanTrominoes.UnaryBlockRightRotationMachine

end
