/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsEndDetectionExecution
import LeanTrominoes.LastRepresentativeEqualityRowsIndexCleanupExecution

/-! # Clearing the row index after last-representative input ends -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def endCleanup_evalsInTime (rowCount : Nat) (tokens : List Token) :
    EvalsToInTime (TM2.step program)
      (scanStartCfg
        ⟨[], List.replicate rowCount (), [], [], [], [], tokens, []⟩)
      (some (reverseOutputCfg ⟨[], [], [], [], [], [], tokens, []⟩))
      (rowCount + 2) := by
  let data : TapeData :=
    ⟨[], List.replicate rowCount (), [], [], [], [], tokens, []⟩
  have first := endDetection_evalsInTime rowCount tokens
  have second := clearRowIndex_evalsInTime
    (List.replicate rowCount ()) data rfl
  have composed := EvalsToInTime.trans (TM2.step program)
    1 (rowCount + 1)
    (scanStartCfg data) (clearRowIndexCfg data)
    (some (reverseOutputCfg { data with rowIndex := [] }))
    (by simpa [data] using first) (by simpa using second)
  simpa [data, Nat.add_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
