/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountIndexSteps

/-! # Copying the unary row index for prefix counting -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def copyIndex_evalsInTime (tokens : List Unit) (data : TapeData)
    (indexEq : data.rowIndex = tokens) :
    EvalsToInTime (TM2.step program) (copyIndexCfg data)
      (some (restoreIndexCfg
        { data with
          rowIndex := []
          indexRestore := tokens.reverse ++ data.indexRestore
          prefixCountdown := tokens.reverse ++ data.prefixCountdown }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_copyIndex_nil data indexEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData :=
        { data with
          rowIndex := tokens
          indexRestore := () :: data.indexRestore
          prefixCountdown := () :: data.prefixCountdown }
      have first := FiniteBlockTransducer.oneStep
        (step_copyIndex_cons data tokens indexEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (copyIndexCfg data) (copyIndexCfg nextData)
        (some (restoreIndexCfg
          { nextData with
            rowIndex := []
            indexRestore := tokens.reverse ++ nextData.indexRestore
            prefixCountdown :=
              tokens.reverse ++ nextData.prefixCountdown }))
        first rest
      convert composed using 1 <;>
        simp [nextData, List.reverse_cons, List.append_assoc]

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
