/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineTapes

/-! # Parser one-step equations for the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace GadgetSparseRouteRecordMachine

def inputState (token : InputToken) : State := some (.inl token)

theorem step_scanPeriod_nil (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step program (scanPeriodCfg data) =
      some (reverseOutputCfg { data with input := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanPeriodCfg, reverseOutputCfg,
    labelCfg, cfg, tapes, loadInput]

theorem step_scanPeriod_unit (data : TapeData) (tail : List InputToken)
    (inputEq : data.input = .unit :: tail) :
    TM2.step program (scanPeriodCfg data) =
      some (scanPeriodCfg
        { data with
          input := tail
          horizontalComplement := () :: data.horizontalComplement }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = .unit :: tail at inputEq
  subst input
  simp [TM2.step, program, scanPeriodCfg, labelCfg, cfg, tapes,
    loadInput, clearGoto, isInputUnitState]

theorem step_scanPeriod_periodEnd (data : TapeData)
    (tail : List InputToken)
    (inputEq : data.input = .periodEnd :: tail) :
    TM2.step program (scanPeriodCfg data) =
      some (scanHorizontalCfg { data with input := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = .periodEnd :: tail at inputEq
  subst input
  simp [TM2.step, program, scanPeriodCfg, scanHorizontalCfg,
    labelCfg, cfg, tapes, loadInput, clearGoto,
    isInputUnitState, isPeriodEndState]

theorem step_scanPeriod_other (data : TapeData)
    (token : InputToken) (tail : List InputToken)
    (inputEq : data.input = token :: tail)
    (notUnit : isInputUnitState (inputState token) = false)
    (notEnd : isPeriodEndState (inputState token) = false) :
    TM2.step program (scanPeriodCfg data) =
      some (cfg .reverseOutput (inputState token)
        { data with input := tail }) := by
  unfold inputState at notUnit notEnd
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = token :: tail at inputEq
  subst input
  simp [TM2.step, program, scanPeriodCfg, cfg, labelCfg, tapes,
    loadInput, inputState, notUnit, notEnd]

theorem step_scanHorizontal_nil (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step program (scanHorizontalCfg data) =
      some (reverseOutputCfg { data with input := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanHorizontalCfg, reverseOutputCfg,
    labelCfg, cfg, tapes, loadInput]

theorem step_scanHorizontal_unit (data : TapeData)
    (tail : List InputToken)
    (inputEq : data.input = .unit :: tail) :
    TM2.step program (scanHorizontalCfg data) =
      some (moveHorizontalCfg (inputState .unit)
        { data with input := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = .unit :: tail at inputEq
  subst input
  simp [TM2.step, program, scanHorizontalCfg, moveHorizontalCfg,
    labelCfg, cfg, tapes, loadInput, inputState,
    isInputUnitState]

theorem step_scanHorizontal_horizontalEnd (data : TapeData)
    (tail : List InputToken)
    (inputEq : data.input = .horizontalEnd :: tail) :
    TM2.step program (scanHorizontalCfg data) =
      some (reserveComplementCfg (inputState .horizontalEnd)
        { data with input := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = .horizontalEnd :: tail at inputEq
  subst input
  simp [TM2.step, program, scanHorizontalCfg, reserveComplementCfg,
    labelCfg, cfg, tapes, loadInput, inputState,
    isInputUnitState, isHorizontalEndState]

theorem step_scanHorizontal_other (data : TapeData)
    (token : InputToken) (tail : List InputToken)
    (inputEq : data.input = token :: tail)
    (notUnit : isInputUnitState (inputState token) = false)
    (notEnd : isHorizontalEndState (inputState token) = false) :
    TM2.step program (scanHorizontalCfg data) =
      some (cfg .reverseOutput (inputState token)
        { data with input := tail }) := by
  unfold inputState at notUnit notEnd
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = token :: tail at inputEq
  subst input
  simp [TM2.step, program, scanHorizontalCfg, cfg, labelCfg, tapes,
    loadInput, inputState, notUnit, notEnd]

theorem step_moveHorizontal_nil (data : TapeData)
    (complementEq : data.horizontalComplement = []) :
    TM2.step program (moveHorizontalCfg (inputState .unit) data) =
      some (reverseOutputCfg
        { data with horizontalComplement := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change complement = [] at complementEq
  subst complement
  simp [TM2.step, program, moveHorizontalCfg, reverseOutputCfg,
    labelCfg, cfg, tapes, loadUnit, inputState]

theorem step_moveHorizontal_cons (data : TapeData)
    (tail : List Unit)
    (complementEq : data.horizontalComplement = () :: tail) :
    TM2.step program (moveHorizontalCfg (inputState .unit) data) =
      some (scanHorizontalCfg
        { data with
          horizontal := () :: data.horizontal
          horizontalComplement := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change complement = () :: tail at complementEq
  subst complement
  simp [TM2.step, program, moveHorizontalCfg, scanHorizontalCfg,
    labelCfg, cfg, tapes, loadUnit, clearGoto, inputState]

theorem step_reserveComplement_nil (data : TapeData)
    (complementEq : data.horizontalComplement = []) :
    TM2.step program
        (reserveComplementCfg (inputState .horizontalEnd) data) =
      some (reverseOutputCfg
        { data with horizontalComplement := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change complement = [] at complementEq
  subst complement
  simp [TM2.step, program, reserveComplementCfg, reverseOutputCfg,
    labelCfg, cfg, tapes, loadUnit, inputState]

theorem step_reserveComplement_cons (data : TapeData)
    (tail : List Unit)
    (complementEq : data.horizontalComplement = () :: tail) :
    TM2.step program
        (reserveComplementCfg (inputState .horizontalEnd) data) =
      some (scanVerticalCfg
        { data with horizontalComplement := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change complement = () :: tail at complementEq
  subst complement
  simp [TM2.step, program, reserveComplementCfg, scanVerticalCfg,
    labelCfg, cfg, tapes, loadUnit, clearGoto, inputState]

theorem step_scanVertical_nil (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step program (scanVerticalCfg data) =
      some (reverseOutputCfg { data with input := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanVerticalCfg, reverseOutputCfg,
    labelCfg, cfg, tapes, loadInput]

theorem step_scanVertical_unit (data : TapeData)
    (tail : List InputToken)
    (inputEq : data.input = .unit :: tail) :
    TM2.step program (scanVerticalCfg data) =
      some (scanVerticalCfg
        { data with
          input := tail
          verticalPositive := () :: data.verticalPositive }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = .unit :: tail at inputEq
  subst input
  simp [TM2.step, program, scanVerticalCfg, labelCfg, cfg, tapes,
    loadInput, clearGoto, isInputUnitState]

theorem step_scanVertical_verticalEnd (data : TapeData)
    (tail : List InputToken)
    (inputEq : data.input = .verticalEnd :: tail) :
    TM2.step program (scanVerticalCfg data) =
      some (scanColorCfg { data with input := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = .verticalEnd :: tail at inputEq
  subst input
  simp [TM2.step, program, scanVerticalCfg, scanColorCfg,
    labelCfg, cfg, tapes, loadInput, clearGoto,
    isInputUnitState, isVerticalEndState]

theorem step_scanVertical_other (data : TapeData)
    (token : InputToken) (tail : List InputToken)
    (inputEq : data.input = token :: tail)
    (notUnit : isInputUnitState (inputState token) = false)
    (notEnd : isVerticalEndState (inputState token) = false) :
    TM2.step program (scanVerticalCfg data) =
      some (cfg .reverseOutput (inputState token)
        { data with input := tail }) := by
  unfold inputState at notUnit notEnd
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = token :: tail at inputEq
  subst input
  simp [TM2.step, program, scanVerticalCfg, cfg, labelCfg, tapes,
    loadInput, inputState, notUnit, notEnd]

theorem step_scanColor_color (state : State) (data : TapeData)
    (color : Gadget.WireColor) (tail : List InputToken)
    (inputEq : data.input = .color color :: tail) :
    TM2.step program (cfg .scanColor state data) =
      some (cfg (.scanIncoming color) (inputState (.color color))
        { data with input := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = .color color :: tail at inputEq
  subst input
  simp [TM2.step, program, cfg, tapes, loadInput, inputState,
    isColorState, colorFromState]

theorem step_scanColor_other (state : State) (data : TapeData)
    (token : InputToken) (tail : List InputToken)
    (inputEq : data.input = token :: tail)
    (notColor : isColorState (inputState token) = false) :
    TM2.step program (cfg .scanColor state data) =
      some (cfg .reverseOutput (inputState token)
        { data with input := tail }) := by
  unfold inputState at notColor
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = token :: tail at inputEq
  subst input
  simp [TM2.step, program, cfg, tapes, loadInput, inputState,
    notColor]

theorem step_scanColor_nil (state : State) (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step program (cfg .scanColor state data) =
      some (reverseOutputCfg { data with input := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, reverseOutputCfg, labelCfg, cfg, tapes,
    loadInput, isColorState]

theorem step_scanIncoming_direction (state : State) (data : TapeData)
    (color : Gadget.WireColor) (direction : AxisDirection)
    (tail : List InputToken)
    (inputEq : data.input = .direction direction :: tail) :
    TM2.step program (cfg (.scanIncoming color) state data) =
      some (advanceCfg color direction
        (inputState (.direction direction)) { data with input := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = .direction direction :: tail at inputEq
  subst input
  simp [TM2.step, program, advanceCfg, cfg, tapes, loadInput,
    inputState, isDirectionState, directionFromState]

theorem step_scanIncoming_other (state : State) (data : TapeData)
    (color : Gadget.WireColor) (token : InputToken)
    (tail : List InputToken)
    (inputEq : data.input = token :: tail)
    (notDirection : isDirectionState (inputState token) = false) :
    TM2.step program (cfg (.scanIncoming color) state data) =
      some (cfg .reverseOutput (inputState token)
        { data with input := tail }) := by
  unfold inputState at notDirection
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = token :: tail at inputEq
  subst input
  simp [TM2.step, program, cfg, tapes, loadInput, inputState,
    notDirection]

theorem step_scanIncoming_nil (state : State) (data : TapeData)
    (color : Gadget.WireColor) (inputEq : data.input = []) :
    TM2.step program (cfg (.scanIncoming color) state data) =
      some (reverseOutputCfg { data with input := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, reverseOutputCfg, labelCfg, cfg, tapes,
    loadInput, isDirectionState]

theorem step_scanOutgoing_direction (data : TapeData)
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (tail : List InputToken)
    (inputEq : data.input = .direction outgoing :: tail) :
    TM2.step program (scanOutgoingCfg color incoming data) =
      some (beginRecordCfg color incoming outgoing
        (inputState (.direction outgoing)) { data with input := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = .direction outgoing :: tail at inputEq
  subst input
  simp [TM2.step, program, scanOutgoingCfg, beginRecordCfg,
    labelCfg, cfg, tapes, loadInput, inputState,
    isDirectionState, directionFromState]

theorem step_scanOutgoing_other (data : TapeData)
    (color : Gadget.WireColor) (incoming : AxisDirection)
    (token : InputToken) (tail : List InputToken)
    (inputEq : data.input = token :: tail)
    (notDirection : isDirectionState (inputState token) = false) :
    TM2.step program (scanOutgoingCfg color incoming data) =
      some (cfg .reverseOutput (inputState token)
        { data with input := tail }) := by
  unfold inputState at notDirection
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = token :: tail at inputEq
  subst input
  simp [TM2.step, program, scanOutgoingCfg, labelCfg, cfg, tapes,
    loadInput, inputState, notDirection]

theorem step_scanOutgoing_nil (data : TapeData)
    (color : Gadget.WireColor) (incoming : AxisDirection)
    (inputEq : data.input = []) :
    TM2.step program (scanOutgoingCfg color incoming data) =
      some (reverseOutputCfg { data with input := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanOutgoingCfg, reverseOutputCfg,
    labelCfg, cfg, tapes, loadInput, isDirectionState]

theorem step_beginRecord (state : State) (data : TapeData)
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection) :
    TM2.step program (beginRecordCfg color incoming outgoing state data) =
      some (copyHorizontalCfg color incoming outgoing data) := by
  simp [TM2.step, program, beginRecordCfg, copyHorizontalCfg,
    clearGoto, labelCfg, cfg]

end GadgetSparseRouteRecordMachine
end LeanTrominoes
