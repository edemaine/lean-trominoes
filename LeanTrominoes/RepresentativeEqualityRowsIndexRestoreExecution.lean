/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsIndexCopyExecution

/-! # Restoring the unary row index -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

/-- Restore the unary row index from its temporary stack. -/
def restoreIndex_evalsInTime (tokens : List Unit) (data : TapeData)
    (restoreEq : data.indexRestore = tokens) :
    EvalsToInTime (TM2.step program) (restoreIndexCfg data)
      (some (scanPrefixCfg true
        { data with
          rowIndex := tokens.reverse ++ data.rowIndex
          indexRestore := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_restoreIndex_nil data restoreEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData :=
        { data with
          rowIndex := () :: data.rowIndex
          indexRestore := tokens }
      have first := oneStep (step_restoreIndex_cons data tokens restoreEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (restoreIndexCfg data) (restoreIndexCfg nextData)
        (some (scanPrefixCfg true
          { nextData with
            rowIndex := tokens.reverse ++ nextData.rowIndex
            indexRestore := [] }))
        first rest
      convert composed using 1 <;>
        simp [nextData, List.reverse_cons, List.append_assoc]

end RepresentativeEqualityRowsMachine
end LeanTrominoes
