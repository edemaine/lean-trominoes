/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsCleanupSteps

/-! # Final unary row-index cleanup -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

/-- Clear the unary row index before reversing the output. -/
def clearRowIndex_evalsInTime (tokens : List Unit) (data : TapeData)
    (indexEq : data.rowIndex = tokens) :
    EvalsToInTime (TM2.step program) (clearRowIndexCfg data)
      (some (reverseOutputCfg { data with rowIndex := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_clearRowIndex_nil data indexEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData := { data with rowIndex := tokens }
      have first := oneStep
        (step_clearRowIndex_cons data tokens indexEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (clearRowIndexCfg data) (clearRowIndexCfg nextData)
        (some (reverseOutputCfg { nextData with rowIndex := [] }))
        first rest
      simpa [nextData] using composed

end RepresentativeEqualityRowsMachine
end LeanTrominoes
