/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsIndexSteps

/-! # Detecting end of last-representative row input -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def endDetection_evalsInTime (rowCount : Nat) (tokens : List Token) :
    EvalsToInTime (TM2.step program)
      (scanStartCfg
        ⟨[], List.replicate rowCount (), [], [], [], [], tokens, []⟩)
      (some (clearRowIndexCfg
        ⟨[], List.replicate rowCount (), [], [], [], [], tokens, []⟩))
      1 := by
  let data : TapeData :=
    ⟨[], List.replicate rowCount (), [], [], [], [], tokens, []⟩
  have step := oneStep (step_scanStart_nil data rfl)
  simpa [data] using step

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
