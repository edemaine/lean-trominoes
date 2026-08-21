/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsSelectedSteps

/-! # Rejected-row clearing steps of the last-representative row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

theorem step_clearRejectedRow_nil (representative : Bool) (data : TapeData)
    (rowEq : data.rowReverse = []) :
    TM2.step program (clearRejectedRowCfg representative data) =
      some (scanStartCfg
        { data with
          rowIndex := () :: data.rowIndex
          rowReverse := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change rowReverse = [] at rowEq
  subst rowReverse
  simp [TM2.step, program, clearRejectedRowCfg, scanStartCfg, idleCfg, cfg,
    tapes, setToken, tokenIsNone, beginRow, initialState]

theorem step_clearRejectedRow_cons (representative : Bool)
    (data : TapeData) (token : Token) (tail : List Token)
    (rowEq : data.rowReverse = token :: tail) :
    TM2.step program (clearRejectedRowCfg representative data) =
      some (clearRejectedRowCfg representative
        { data with rowReverse := tail }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change rowReverse = token :: tail at rowEq
  subst rowReverse
  simp [TM2.step, program, clearRejectedRowCfg, cfg, tapes, setToken,
    tokenIsNone, clearToken]

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
