/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsRejectedSteps

/-! # Final cleanup steps of the last-representative row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

theorem step_clearRowIndex_nil (data : TapeData)
    (indexEq : data.rowIndex = []) :
    TM2.step program (clearRowIndexCfg data) =
      some (reverseOutputCfg { data with rowIndex := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change rowIndex = [] at indexEq
  subst rowIndex
  simp [TM2.step, program, clearRowIndexCfg, reverseOutputCfg, idleCfg,
    cfg, tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_clearRowIndex_cons (data : TapeData) (tail : List Unit)
    (indexEq : data.rowIndex = () :: tail) :
    TM2.step program (clearRowIndexCfg data) =
      some (clearRowIndexCfg { data with rowIndex := tail }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change rowIndex = () :: tail at indexEq
  subst rowIndex
  simp [TM2.step, program, clearRowIndexCfg, idleCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_reverseOutput_nil (output : List Token) :
    TM2.step program
        (reverseOutputCfg ⟨[], [], [], [], [], [], [], output⟩) =
      some (haltCfg output) := by
  simp [TM2.step, program, reverseOutputCfg, haltCfg, idleCfg, cfg, tapes,
    setToken, tokenIsNone, initialState]

theorem step_reverseOutput_cons (token : Token) (tokens output : List Token) :
    TM2.step program
        (reverseOutputCfg
          ⟨[], [], [], [], [], [], token :: tokens, output⟩) =
      some (reverseOutputCfg
        ⟨[], [], [], [], [], [], tokens, token :: output⟩) := by
  simp [TM2.step, program, reverseOutputCfg, idleCfg, cfg, tapes, setToken,
    tokenIsNone, tokenFromState, clearToken, initialState]

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
