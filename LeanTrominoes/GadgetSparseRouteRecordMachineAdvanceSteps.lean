/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineParserSteps

/-! # Counter-transition steps for the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace GadgetSparseRouteRecordMachine

theorem step_advance_east_cons (state : State) (data : TapeData)
    (color : Gadget.WireColor) (tail : List Unit)
    (complementEq : data.horizontalComplement = () :: tail) :
    TM2.step program (advanceCfg color .east state data) =
      some (scanOutgoingCfg color .east
        { data with
          horizontal := () :: data.horizontal
          horizontalComplement := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change complement = () :: tail at complementEq
  subst complement
  simp [TM2.step, program, advanceCfg, scanOutgoingCfg, afterAdvance,
    clearGoto, labelCfg, cfg, tapes, loadUnit]

theorem step_advance_east_nil (state : State) (data : TapeData)
    (color : Gadget.WireColor)
    (complementEq : data.horizontalComplement = []) :
    TM2.step program (advanceCfg color .east state data) =
      some (wrapEastCfg color .east
        { data with horizontalComplement := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change complement = [] at complementEq
  subst complement
  simp [TM2.step, program, advanceCfg, wrapEastCfg,
    labelCfg, cfg, tapes, loadUnit]

theorem step_wrapEast_cons (data : TapeData)
    (color : Gadget.WireColor) (tail : List Unit)
    (horizontalEq : data.horizontal = () :: tail) :
    TM2.step program (wrapEastCfg color .east data) =
      some (wrapEastCfg color .east
        { data with
          horizontal := tail
          horizontalComplement := () :: data.horizontalComplement }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change horizontal = () :: tail at horizontalEq
  subst horizontal
  simp [TM2.step, program, wrapEastCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

theorem step_wrapEast_nil (data : TapeData)
    (color : Gadget.WireColor) (horizontalEq : data.horizontal = []) :
    TM2.step program (wrapEastCfg color .east data) =
      some (scanOutgoingCfg color .east
        { data with horizontal := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change horizontal = [] at horizontalEq
  subst horizontal
  simp [TM2.step, program, wrapEastCfg, scanOutgoingCfg,
    afterAdvance, clearGoto, labelCfg, cfg, tapes, loadUnit]

theorem step_advance_west_cons (state : State) (data : TapeData)
    (color : Gadget.WireColor) (tail : List Unit)
    (horizontalEq : data.horizontal = () :: tail) :
    TM2.step program (advanceCfg color .west state data) =
      some (scanOutgoingCfg color .west
        { data with
          horizontal := tail
          horizontalComplement := () :: data.horizontalComplement }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change horizontal = () :: tail at horizontalEq
  subst horizontal
  simp [TM2.step, program, advanceCfg, scanOutgoingCfg, afterAdvance,
    clearGoto, labelCfg, cfg, tapes, loadUnit]

theorem step_advance_west_nil (state : State) (data : TapeData)
    (color : Gadget.WireColor) (horizontalEq : data.horizontal = []) :
    TM2.step program (advanceCfg color .west state data) =
      some (wrapWestCfg color .west { data with horizontal := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change horizontal = [] at horizontalEq
  subst horizontal
  simp [TM2.step, program, advanceCfg, wrapWestCfg,
    labelCfg, cfg, tapes, loadUnit]

theorem step_wrapWest_cons (data : TapeData)
    (color : Gadget.WireColor) (tail : List Unit)
    (complementEq : data.horizontalComplement = () :: tail) :
    TM2.step program (wrapWestCfg color .west data) =
      some (wrapWestCfg color .west
        { data with
          horizontal := () :: data.horizontal
          horizontalComplement := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change complement = () :: tail at complementEq
  subst complement
  simp [TM2.step, program, wrapWestCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

theorem step_wrapWest_nil (data : TapeData)
    (color : Gadget.WireColor)
    (complementEq : data.horizontalComplement = []) :
    TM2.step program (wrapWestCfg color .west data) =
      some (scanOutgoingCfg color .west
        { data with horizontalComplement := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change complement = [] at complementEq
  subst complement
  simp [TM2.step, program, wrapWestCfg, scanOutgoingCfg,
    afterAdvance, clearGoto, labelCfg, cfg, tapes, loadUnit]

theorem step_advance_north_positive (state : State) (data : TapeData)
    (color : Gadget.WireColor) (tail : List Unit)
    (positiveEq : data.verticalPositive = () :: tail) :
    TM2.step program (advanceCfg color .north state data) =
      some (scanOutgoingCfg color .north
        { data with verticalPositive := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change positive = () :: tail at positiveEq
  subst positive
  simp [TM2.step, program, advanceCfg, scanOutgoingCfg, afterAdvance,
    clearGoto, labelCfg, cfg, tapes, loadUnit]

theorem step_advance_north_nonpositive (state : State)
    (data : TapeData) (color : Gadget.WireColor)
    (positiveEq : data.verticalPositive = []) :
    TM2.step program (advanceCfg color .north state data) =
      some (scanOutgoingCfg color .north
        { data with
          verticalPositive := []
          verticalNegative := () :: data.verticalNegative }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change positive = [] at positiveEq
  subst positive
  simp [TM2.step, program, advanceCfg, scanOutgoingCfg, afterAdvance,
    clearGoto, labelCfg, cfg, tapes, loadUnit]

theorem step_advance_south_negative (state : State) (data : TapeData)
    (color : Gadget.WireColor) (tail : List Unit)
    (negativeEq : data.verticalNegative = () :: tail) :
    TM2.step program (advanceCfg color .south state data) =
      some (scanOutgoingCfg color .south
        { data with verticalNegative := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change negative = () :: tail at negativeEq
  subst negative
  simp [TM2.step, program, advanceCfg, scanOutgoingCfg, afterAdvance,
    clearGoto, labelCfg, cfg, tapes, loadUnit]

theorem step_advance_south_nonnegative (state : State)
    (data : TapeData) (color : Gadget.WireColor)
    (negativeEq : data.verticalNegative = []) :
    TM2.step program (advanceCfg color .south state data) =
      some (scanOutgoingCfg color .south
        { data with
          verticalPositive := () :: data.verticalPositive
          verticalNegative := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change negative = [] at negativeEq
  subst negative
  simp [TM2.step, program, advanceCfg, scanOutgoingCfg, afterAdvance,
    clearGoto, labelCfg, cfg, tapes, loadUnit]

theorem step_advance_invalid (state : State) (data : TapeData)
    (color : Gadget.WireColor) :
    TM2.step program (advanceCfg color .invalid state data) =
      some (scanOutgoingCfg color .invalid data) := by
  simp [TM2.step, program, advanceCfg, scanOutgoingCfg,
    afterAdvance, clearGoto, labelCfg, cfg]

end GadgetSparseRouteRecordMachine
end LeanTrominoes
