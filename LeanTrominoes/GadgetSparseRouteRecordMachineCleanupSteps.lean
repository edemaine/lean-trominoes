/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineTapes

/-! # Terminal cleanup steps for the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace GadgetSparseRouteRecordMachine

theorem step_clearInput_nil (state : State) (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step program (clearInputCfg state data) =
      some (clearHorizontalCfg { data with input := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, clearInputCfg, clearHorizontalCfg,
    labelCfg, cfg, tapes, loadInput]

theorem step_clearInput_cons (state : State) (data : TapeData)
    (token : InputToken) (tail : List InputToken)
    (inputEq : data.input = token :: tail) :
    TM2.step program (clearInputCfg state data) =
      some (clearInputCfg none { data with input := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change input = token :: tail at inputEq
  subst input
  simp [TM2.step, program, clearInputCfg, clearGoto, cfg, tapes, loadInput]

theorem step_clearHorizontal_nil (data : TapeData)
    (horizontalEq : data.horizontal = []) :
    TM2.step program (clearHorizontalCfg data) =
      some (clearHorizontalComplementCfg
        { data with horizontal := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change horizontal = [] at horizontalEq
  subst horizontal
  simp [TM2.step, program, clearHorizontalCfg,
    clearHorizontalComplementCfg, labelCfg, cfg, tapes, loadUnit]

theorem step_clearHorizontal_cons (data : TapeData) (tail : List Unit)
    (horizontalEq : data.horizontal = () :: tail) :
    TM2.step program (clearHorizontalCfg data) =
      some (clearHorizontalCfg { data with horizontal := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change horizontal = () :: tail at horizontalEq
  subst horizontal
  simp [TM2.step, program, clearHorizontalCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

theorem step_clearHorizontalComplement_nil (data : TapeData)
    (complementEq : data.horizontalComplement = []) :
    TM2.step program (clearHorizontalComplementCfg data) =
      some (clearVerticalPositiveCfg
        { data with horizontalComplement := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change complement = [] at complementEq
  subst complement
  simp [TM2.step, program, clearHorizontalComplementCfg,
    clearVerticalPositiveCfg, labelCfg, cfg, tapes, loadUnit]

theorem step_clearHorizontalComplement_cons (data : TapeData)
    (tail : List Unit)
    (complementEq : data.horizontalComplement = () :: tail) :
    TM2.step program (clearHorizontalComplementCfg data) =
      some (clearHorizontalComplementCfg
        { data with horizontalComplement := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change complement = () :: tail at complementEq
  subst complement
  simp [TM2.step, program, clearHorizontalComplementCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

theorem step_clearVerticalPositive_nil (data : TapeData)
    (positiveEq : data.verticalPositive = []) :
    TM2.step program (clearVerticalPositiveCfg data) =
      some (clearVerticalNegativeCfg
        { data with verticalPositive := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change positive = [] at positiveEq
  subst positive
  simp [TM2.step, program, clearVerticalPositiveCfg,
    clearVerticalNegativeCfg, labelCfg, cfg, tapes, loadUnit]

theorem step_clearVerticalPositive_cons (data : TapeData)
    (tail : List Unit) (positiveEq : data.verticalPositive = () :: tail) :
    TM2.step program (clearVerticalPositiveCfg data) =
      some (clearVerticalPositiveCfg
        { data with verticalPositive := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change positive = () :: tail at positiveEq
  subst positive
  simp [TM2.step, program, clearVerticalPositiveCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

theorem step_clearVerticalNegative_nil (data : TapeData)
    (negativeEq : data.verticalNegative = []) :
    TM2.step program (clearVerticalNegativeCfg data) =
      some (clearScratchCfg { data with verticalNegative := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change negative = [] at negativeEq
  subst negative
  simp [TM2.step, program, clearVerticalNegativeCfg, clearScratchCfg,
    labelCfg, cfg, tapes, loadUnit]

theorem step_clearVerticalNegative_cons (data : TapeData)
    (tail : List Unit) (negativeEq : data.verticalNegative = () :: tail) :
    TM2.step program (clearVerticalNegativeCfg data) =
      some (clearVerticalNegativeCfg
        { data with verticalNegative := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change negative = () :: tail at negativeEq
  subst negative
  simp [TM2.step, program, clearVerticalNegativeCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

theorem step_clearScratch_nil (data : TapeData)
    (scratchEq : data.scratch = []) :
    TM2.step program (clearScratchCfg data) =
      some (haltCfg { data with scratch := [] }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, clearScratchCfg, haltCfg,
    labelCfg, cfg, tapes, loadUnit]

theorem step_clearScratch_cons (data : TapeData) (tail : List Unit)
    (scratchEq : data.scratch = () :: tail) :
    TM2.step program (clearScratchCfg data) =
      some (clearScratchCfg { data with scratch := tail }) := by
  rcases data with ⟨input, horizontal, complement, positive, negative,
    scratch, outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, clearScratchCfg, clearGoto,
    labelCfg, cfg, tapes, loadUnit]

end GadgetSparseRouteRecordMachine
end LeanTrominoes
