/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsFinalCleanupExecution
import LeanTrominoes.LastRepresentativeEqualityRowsListExecution

/-! # Complete execution of the last-representative row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def totalTime (rows : List (List Bool)) : Nat :=
  finalCleanupTime rows.length
      (LastRepresentativeEqualityRowTokens.tokensAux 0 rows) +
    rowsTime 0 rows

def execution_evalsInTime (rows : List (List Bool)) :
    EvalsToInTime (TM2.step program)
      (scanStartCfg
        ⟨DelimitedBinaryWords.encode ⟨rows⟩, [], [], [], [], [], [], []⟩)
      (some (haltCfg
        (LastRepresentativeEqualityRowTokens.tokensAux 0 rows)))
      (totalTime rows) := by
  let tokens := LastRepresentativeEqualityRowTokens.tokensAux 0 rows
  let initial : TapeData :=
    ⟨DelimitedBinaryWords.encode ⟨rows⟩, [], [], [], [], [], [], []⟩
  have first := rows_evalsInTime 0 rows [] initial
    (by simp [initial]) (by simp [initial]) (by simp [initial])
    (by simp [initial]) (by simp [initial]) (by simp [initial])
  have first' :
      EvalsToInTime (TM2.step program) (scanStartCfg initial)
        (some (scanStartCfg
          ⟨[], List.replicate rows.length (), [], [], [], [],
            tokens.reverse, []⟩))
        (rowsTime 0 rows) := by
    simpa [initial, tokens] using first
  have second := finalCleanup_evalsInTime rows.length tokens
  have composed := EvalsToInTime.trans (TM2.step program)
    (rowsTime 0 rows) (finalCleanupTime rows.length tokens)
    (scanStartCfg initial)
    (scanStartCfg
      ⟨[], List.replicate rows.length (), [], [], [], [],
        tokens.reverse, []⟩)
    (some (haltCfg tokens))
    first' second
  simpa [totalTime, initial, tokens] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
