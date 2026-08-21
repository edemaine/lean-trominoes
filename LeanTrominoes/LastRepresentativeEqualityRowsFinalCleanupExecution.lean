/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsEndCleanupExecution
import LeanTrominoes.LastRepresentativeEqualityRowsReverseExecution

/-! # Terminal cleanup of the last-representative row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def finalCleanupTime (rowCount : Nat) (tokens : List Token) : Nat :=
  tokens.length + rowCount + 3

def finalCleanup_evalsInTime (rowCount : Nat) (tokens : List Token) :
    EvalsToInTime (TM2.step program)
      (scanStartCfg
        ⟨[], List.replicate rowCount (), [], [], [], [], tokens.reverse, []⟩)
      (some (haltCfg tokens))
      (finalCleanupTime rowCount tokens) := by
  have first := endCleanup_evalsInTime rowCount tokens.reverse
  have second := reverseOutput_evalsInTime tokens.reverse []
  have composed := EvalsToInTime.trans (TM2.step program)
    (rowCount + 2) (tokens.length + 1)
    (scanStartCfg
      ⟨[], List.replicate rowCount (), [], [], [], [], tokens.reverse, []⟩)
    (reverseOutputCfg
      ⟨[], [], [], [], [], [], tokens.reverse, []⟩)
    (some (haltCfg tokens))
    first (by simpa using second)
  simpa [finalCleanupTime, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
