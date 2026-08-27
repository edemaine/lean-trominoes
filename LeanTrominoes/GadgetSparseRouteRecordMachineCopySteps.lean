/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineAdvanceSteps

/-! # Record-copy and reversal steps for the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction

theorem step_copyHorizontal_nil (data : TapeData)
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (horizontalEq : data.horizontal = []) :
    TM2.step program (copyHorizontalCfg color incoming outgoing data) =
      some (restoreHorizontalCfg color incoming outgoing
        { data with
          horizontal := []
          outputReverse := .fieldEnd :: data.outputReverse }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change horizontal = [] at horizontalEq
  subst horizontal
  simp [TM2.step, program, copyHorizontalCfg, restoreHorizontalCfg,
    labelCfg, cfg, tapes, loadUnit]

theorem step_copyHorizontal_cons (data : TapeData)
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (tail : List Unit) (horizontalEq : data.horizontal = () :: tail) :
    TM2.step program (copyHorizontalCfg color incoming outgoing data) =
      some (copyHorizontalCfg color incoming outgoing
        { data with
          horizontal := tail
          scratch := () :: data.scratch
          outputReverse := .coordinateUnit :: data.outputReverse }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change horizontal = () :: tail at horizontalEq
  subst horizontal
  simp [TM2.step, program, copyHorizontalCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

theorem step_restoreHorizontal_nil (data : TapeData)
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (scratchEq : data.scratch = []) :
    TM2.step program (restoreHorizontalCfg color incoming outgoing data) =
      some (copyVerticalCfg color incoming outgoing
        { data with scratch := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, restoreHorizontalCfg, copyVerticalCfg,
    labelCfg, cfg, tapes, loadUnit]

theorem step_restoreHorizontal_cons (data : TapeData)
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (tail : List Unit) (scratchEq : data.scratch = () :: tail) :
    TM2.step program (restoreHorizontalCfg color incoming outgoing data) =
      some (restoreHorizontalCfg color incoming outgoing
        { data with
          horizontal := () :: data.horizontal
          scratch := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restoreHorizontalCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

theorem step_copyVertical_nil (data : TapeData)
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (positiveEq : data.verticalPositive = []) :
    TM2.step program (copyVerticalCfg color incoming outgoing data) =
      some (restoreVerticalCfg color incoming outgoing
        { data with
          verticalPositive := []
          outputReverse :=
            .cellType (routingCellTypeFromForwardDirections
              incoming outgoing color) :: data.outputReverse }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change positive = [] at positiveEq
  subst positive
  simp [TM2.step, program, copyVerticalCfg, restoreVerticalCfg,
    labelCfg, cfg, tapes, loadUnit]

theorem step_copyVertical_cons (data : TapeData)
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (tail : List Unit) (positiveEq : data.verticalPositive = () :: tail) :
    TM2.step program (copyVerticalCfg color incoming outgoing data) =
      some (copyVerticalCfg color incoming outgoing
        { data with
          verticalPositive := tail
          scratch := () :: data.scratch
          outputReverse := .coordinateUnit :: data.outputReverse }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change positive = () :: tail at positiveEq
  subst positive
  simp [TM2.step, program, copyVerticalCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

theorem step_restoreVertical_nil (data : TapeData)
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (scratchEq : data.scratch = []) :
    TM2.step program (restoreVerticalCfg color incoming outgoing data) =
      some (advanceCfg color outgoing none { data with scratch := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, restoreVerticalCfg, advanceCfg,
    labelCfg, cfg, tapes, loadUnit]

theorem step_restoreVertical_cons (data : TapeData)
    (color : Gadget.WireColor) (incoming outgoing : AxisDirection)
    (tail : List Unit) (scratchEq : data.scratch = () :: tail) :
    TM2.step program (restoreVerticalCfg color incoming outgoing data) =
      some (restoreVerticalCfg color incoming outgoing
        { data with
          verticalPositive := () :: data.verticalPositive
          scratch := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restoreVerticalCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

theorem step_reverseOutput_nil (state : State) (data : TapeData)
    (reverseEq : data.outputReverse = []) :
    TM2.step program (cfg .reverseOutput state data) =
      some (clearInputCfg none { data with outputReverse := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change outputReverse = [] at reverseEq
  subst outputReverse
  simp [TM2.step, program, clearInputCfg, cfg, tapes, loadOutput]

theorem step_reverseOutput_cons (state : State) (data : TapeData)
    (token : OutputToken) (tail : List OutputToken)
    (reverseEq : data.outputReverse = token :: tail) :
    TM2.step program (cfg .reverseOutput state data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := token :: data.output }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change outputReverse = token :: tail at reverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, clearGoto,
    labelCfg, cfg, tapes, loadOutput, outputFromState]

end GadgetSparseRouteRecordMachine
end LeanTrominoes
