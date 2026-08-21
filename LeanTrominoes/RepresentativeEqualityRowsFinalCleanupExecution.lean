/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsIndexCleanupExecution
import LeanTrominoes.RepresentativeEqualityRowsIndexSteps
import LeanTrominoes.RepresentativeEqualityRowsReverseExecution

/-! # Terminal cleanup of the representative equality-row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

def finalCleanupTime (rowCount : Nat) (tokens : List Token) : Nat :=
  tokens.length + rowCount + 3

/-- Clear the final unary index and reverse the accumulated selected rows. -/
def finalCleanup_evalsInTime (rowCount : Nat) (tokens : List Token) :
    EvalsToInTime (TM2.step program)
      (scanStartCfg
        ⟨[], List.replicate rowCount (), [], [], [], [], tokens.reverse, []⟩)
      (some (haltCfg tokens))
      (finalCleanupTime rowCount tokens) := by
  let data : TapeData :=
    ⟨[], List.replicate rowCount (), [], [], [], [], tokens.reverse, []⟩
  have first := oneStep (step_scanStart_nil data rfl)
  have cleared := clearRowIndex_evalsInTime
    (List.replicate rowCount ()) { data with input := [] } rfl
  have throughIndex := EvalsToInTime.trans (TM2.step program)
    1 (rowCount + 1)
    (scanStartCfg data)
    (clearRowIndexCfg { data with input := [] })
    (some (reverseOutputCfg
      { data with input := [], rowIndex := [] }))
    first (by simpa using cleared)
  have reversed := reverseOutput_evalsInTime tokens.reverse []
  have composed := EvalsToInTime.trans (TM2.step program)
    (rowCount + 2) (tokens.length + 1)
    (scanStartCfg data)
    (reverseOutputCfg
      { data with input := [], rowIndex := [] })
    (some (haltCfg tokens))
    (by simpa [data, Nat.add_assoc] using throughIndex)
    (by simpa using reversed)
  simpa [finalCleanupTime, data, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using composed

end RepresentativeEqualityRowsMachine
end LeanTrominoes
