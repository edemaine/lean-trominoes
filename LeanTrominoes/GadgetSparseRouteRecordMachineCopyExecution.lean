/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCopySteps
import LeanTrominoes.FiniteBlockTransducer

/-! # Coordinate-copy executions for the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

/-- Reverse-stack contribution after copying a horizontal coordinate. -/
def horizontalReverse (count : Nat) : List OutputToken :=
  .fieldEnd :: List.replicate count .coordinateUnit

theorem horizontalReverse_succ (count : Nat)
    (tail : List OutputToken) :
    horizontalReverse count ++ .coordinateUnit :: tail =
      horizontalReverse (count + 1) ++ tail := by
  simp [horizontalReverse, List.replicate_succ', List.append_assoc]

/-- Drain the horizontal coordinate onto scratch and reverse output. -/
def copyHorizontal_evalsInTime
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (word : List Unit) (data : TapeData)
    (horizontalEq : data.horizontal = word) :
    EvalsToInTime (TM2.step program)
      (copyHorizontalCfg color incoming outgoing data)
      (some (restoreHorizontalCfg color incoming outgoing
        { data with
          horizontal := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            horizontalReverse word.length ++ data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_copyHorizontal_nil data color incoming outgoing horizontalEq)
      convert step using 1 <;> simp [horizontalReverse]
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with
          horizontal := word
          scratch := () :: data.scratch
          outputReverse := .coordinateUnit :: data.outputReverse }
      have first := oneStep
        (step_copyHorizontal_cons data color incoming outgoing word
          horizontalEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (copyHorizontalCfg color incoming outgoing data)
        (copyHorizontalCfg color incoming outgoing nextData)
        (some (restoreHorizontalCfg color incoming outgoing
          { nextData with
            horizontal := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse := horizontalReverse word.length ++
              nextData.outputReverse })) first rest
      convert composed using 1
      · simp only [nextData, List.reverse_cons, List.append_assoc,
          List.singleton_append, List.length_cons]
        rw [horizontalReverse_succ]
      · simp

/-- Restore a drained horizontal coordinate. -/
def restoreHorizontal_evalsInTime
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (word : List Unit) (data : TapeData)
    (scratchEq : data.scratch = word) :
    EvalsToInTime (TM2.step program)
      (restoreHorizontalCfg color incoming outgoing data)
      (some (copyVerticalCfg color incoming outgoing
        { data with
          horizontal := word.reverse ++ data.horizontal
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreHorizontal_nil data color incoming outgoing scratchEq)
      convert step using 1 <;> simp
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with horizontal := () :: data.horizontal, scratch := word }
      have first := oneStep
        (step_restoreHorizontal_cons data color incoming outgoing word
          scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (restoreHorizontalCfg color incoming outgoing data)
        (restoreHorizontalCfg color incoming outgoing nextData)
        (some (copyVerticalCfg color incoming outgoing
          { nextData with
            horizontal := word.reverse ++ nextData.horizontal
            scratch := [] })) first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- Copy and restore the full horizontal coordinate. -/
def copyHorizontalThrough_evalsInTime
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (word : List Unit) (data : TapeData)
    (horizontalEq : data.horizontal = word)
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (copyHorizontalCfg color incoming outgoing data)
      (some (copyVerticalCfg color incoming outgoing
        { data with
          horizontal := word
          scratch := []
          outputReverse :=
            horizontalReverse word.length ++ data.outputReverse }))
      (2 * word.length + 2) := by
  have copied := copyHorizontal_evalsInTime color incoming outgoing
    word data horizontalEq
  let copiedData : TapeData :=
    { data with
      horizontal := []
      scratch := word.reverse ++ data.scratch
      outputReverse :=
        horizontalReverse word.length ++ data.outputReverse }
  have restored := restoreHorizontal_evalsInTime color incoming outgoing
    word.reverse copiedData (by simp [copiedData, scratchEq])
  have composed := EvalsToInTime.trans (TM2.step program)
    (word.length + 1) (word.reverse.length + 1)
    (copyHorizontalCfg color incoming outgoing data)
    (restoreHorizontalCfg color incoming outgoing copiedData)
    (some (copyVerticalCfg color incoming outgoing
      { copiedData with
        horizontal := word.reverse.reverse ++ copiedData.horizontal
        scratch := [] })) copied (by simpa [copiedData] using restored)
  convert composed using 1
  · simp [copiedData]
  · simp
    omega

/-- Reverse-stack contribution after copying a positive vertical
coordinate and selecting its finite cell type. -/
def verticalReverse (count : Nat)
    (cellType : Gadget.OrthogonalCellType) : List OutputToken :=
  .cellType cellType :: List.replicate count .coordinateUnit

theorem verticalReverse_succ (count : Nat)
    (cellType : Gadget.OrthogonalCellType) (tail : List OutputToken) :
    verticalReverse count cellType ++ .coordinateUnit :: tail =
      verticalReverse (count + 1) cellType ++ tail := by
  simp [verticalReverse, List.replicate_succ', List.append_assoc]

/-- Drain the positive vertical coordinate onto scratch and reverse output. -/
def copyVertical_evalsInTime
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (word : List Unit) (data : TapeData)
    (positiveEq : data.verticalPositive = word) :
    let cellType := routingCellTypeFromForwardDirections
      incoming outgoing color
    EvalsToInTime (TM2.step program)
      (copyVerticalCfg color incoming outgoing data)
      (some (restoreVerticalCfg color incoming outgoing
        { data with
          verticalPositive := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            verticalReverse word.length cellType ++ data.outputReverse }))
      (word.length + 1) := by
  dsimp only
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_copyVertical_nil data color incoming outgoing positiveEq)
      convert step using 1 <;> simp [verticalReverse]
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with
          verticalPositive := word
          scratch := () :: data.scratch
          outputReverse := .coordinateUnit :: data.outputReverse }
      have first := oneStep
        (step_copyVertical_cons data color incoming outgoing word positiveEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (copyVerticalCfg color incoming outgoing data)
        (copyVerticalCfg color incoming outgoing nextData)
        (some (restoreVerticalCfg color incoming outgoing
          { nextData with
            verticalPositive := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse := verticalReverse word.length
              (routingCellTypeFromForwardDirections incoming outgoing color) ++
                nextData.outputReverse })) first rest
      convert composed using 1
      · simp only [nextData, List.reverse_cons, List.append_assoc,
          List.singleton_append, List.length_cons]
        rw [verticalReverse_succ]
      · simp

/-- Restore the drained positive vertical coordinate and continue with the
outgoing direction transition. -/
def restoreVertical_evalsInTime
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (word : List Unit) (data : TapeData)
    (scratchEq : data.scratch = word) :
    EvalsToInTime (TM2.step program)
      (restoreVerticalCfg color incoming outgoing data)
      (some (advanceCfg color outgoing none
        { data with
          verticalPositive := word.reverse ++ data.verticalPositive
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreVertical_nil data color incoming outgoing scratchEq)
      convert step using 1 <;> simp
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with
          verticalPositive := () :: data.verticalPositive
          scratch := word }
      have first := oneStep
        (step_restoreVertical_cons data color incoming outgoing word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (restoreVerticalCfg color incoming outgoing data)
        (restoreVerticalCfg color incoming outgoing nextData)
        (some (advanceCfg color outgoing none
          { nextData with
            verticalPositive := word.reverse ++ nextData.verticalPositive
            scratch := [] })) first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- Copy and restore the positive vertical coordinate. -/
def copyVerticalThrough_evalsInTime
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (word : List Unit) (data : TapeData)
    (positiveEq : data.verticalPositive = word)
    (scratchEq : data.scratch = []) :
    let cellType := routingCellTypeFromForwardDirections
      incoming outgoing color
    EvalsToInTime (TM2.step program)
      (copyVerticalCfg color incoming outgoing data)
      (some (advanceCfg color outgoing none
        { data with
          verticalPositive := word
          scratch := []
          outputReverse :=
            verticalReverse word.length cellType ++ data.outputReverse }))
      (2 * word.length + 2) := by
  dsimp only
  have copied := copyVertical_evalsInTime color incoming outgoing
    word data positiveEq
  let copiedData : TapeData :=
    { data with
      verticalPositive := []
      scratch := word.reverse ++ data.scratch
      outputReverse :=
        verticalReverse word.length
          (routingCellTypeFromForwardDirections incoming outgoing color) ++
            data.outputReverse }
  have restored := restoreVertical_evalsInTime color incoming outgoing
    word.reverse copiedData (by simp [copiedData, scratchEq])
  have composed := EvalsToInTime.trans (TM2.step program)
    (word.length + 1) (word.reverse.length + 1)
    (copyVerticalCfg color incoming outgoing data)
    (restoreVerticalCfg color incoming outgoing copiedData)
    (some (advanceCfg color outgoing none
      { copiedData with
        verticalPositive := word.reverse.reverse ++
          copiedData.verticalPositive
        scratch := [] })) copied (by simpa [copiedData] using restored)
  convert composed using 1
  · simp [copiedData]
  · simp
    omega

theorem recordReverse_eq (horizontal vertical : Nat)
    (cellType : Gadget.OrthogonalCellType) :
    verticalReverse vertical cellType ++ horizontalReverse horizontal =
      (GadgetSparseAssignmentTokens.assignmentTokens
        ((((horizontal : Nat) : Int), ((vertical : Nat) : Int)),
          cellType)).reverse := by
  unfold verticalReverse horizontalReverse
    GadgetSparseAssignmentTokens.assignmentTokens
  simp only [Int.toNat_natCast, List.reverse_append,
    List.reverse_cons, List.reverse_replicate]
  simp [List.append_assoc]

/-- Emit one complete canonical record and arrive at the outgoing direction
transition with all copied counters restored. -/
def record_evalsInTime
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (horizontal positive : List Unit) (data : TapeData)
    (horizontalEq : data.horizontal = horizontal)
    (positiveEq : data.verticalPositive = positive)
    (scratchEq : data.scratch = []) :
    let cellType := routingCellTypeFromForwardDirections
      incoming outgoing color
    EvalsToInTime (TM2.step program)
      (beginRecordCfg color incoming outgoing (inputState (.direction outgoing))
        data)
      (some (advanceCfg color outgoing none
        { data with
          horizontal := horizontal
          verticalPositive := positive
          scratch := []
          outputReverse :=
            verticalReverse positive.length cellType ++
              horizontalReverse horizontal.length ++ data.outputReverse }))
      (2 * horizontal.length + 2 * positive.length + 5) := by
  dsimp only
  have begun := oneStep (step_beginRecord
    (inputState (.direction outgoing)) data color incoming outgoing)
  have horizontalCopied := copyHorizontalThrough_evalsInTime
    color incoming outgoing horizontal data horizontalEq scratchEq
  let afterHorizontal : TapeData :=
    { data with
      horizontal := horizontal
      scratch := []
      outputReverse :=
        horizontalReverse horizontal.length ++ data.outputReverse }
  have verticalCopied := copyVerticalThrough_evalsInTime
    color incoming outgoing positive afterHorizontal
    (by simpa [afterHorizontal] using positiveEq) (by simp [afterHorizontal])
  have firstTwo := EvalsToInTime.trans (TM2.step program)
    1 (2 * horizontal.length + 2)
    (beginRecordCfg color incoming outgoing (inputState (.direction outgoing))
      data)
    (copyHorizontalCfg color incoming outgoing data)
    (some (copyVerticalCfg color incoming outgoing afterHorizontal))
    begun (by simpa [afterHorizontal] using horizontalCopied)
  have whole := EvalsToInTime.trans (TM2.step program)
    (2 * horizontal.length + 2 + 1) (2 * positive.length + 2)
    (beginRecordCfg color incoming outgoing (inputState (.direction outgoing))
      data)
    (copyVerticalCfg color incoming outgoing afterHorizontal)
    (some (advanceCfg color outgoing none
      { afterHorizontal with
        verticalPositive := positive
        scratch := []
        outputReverse := verticalReverse positive.length
          (routingCellTypeFromForwardDirections incoming outgoing color) ++
            afterHorizontal.outputReverse })) firstTwo
      (by simpa [afterHorizontal] using verticalCopied)
  convert whole using 1
  · simp [afterHorizontal, List.append_assoc]
  · omega

/-- Reverse an accumulated word onto the final output tape. -/
def reverseOutput_evalsInTime (state : State)
    (word : List OutputToken) (data : TapeData)
    (outputReverseEq : data.outputReverse = word) :
    EvalsToInTime (TM2.step program)
      (cfg .reverseOutput state data)
      (some (haltCfg
        { data with
          outputReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing state data with
  | nil =>
      have step := oneStep (step_reverseOutput_nil state data
        outputReverseEq)
      convert step using 1 <;> simp
  | cons token word induction =>
      let nextData : TapeData :=
        { data with
          outputReverse := word
          output := token :: data.output }
      have first := oneStep
        (step_reverseOutput_cons state data token word outputReverseEq)
      have rest := induction none nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (cfg .reverseOutput state data) (reverseOutputCfg nextData)
        (some (haltCfg
          { nextData with
            outputReverse := []
            output := word.reverse ++ nextData.output })) first
          (by simpa [reverseOutputCfg, labelCfg] using rest)
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
