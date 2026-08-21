/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsSuffixSteps

/-! # Execution of strict-suffix inspection -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

/-- Inspect every strict-suffix bit and copy the suffix delimiter. -/
def scanSuffixBits_evalsInTime (representative : Bool) (bits : List Bool)
    (tail : List Token) (data : TapeData)
    (inputEq : data.input = bits.map .bit ++ .wordEnd :: tail) :
    EvalsToInTime (TM2.step program) (scanSuffixCfg representative data)
      (some (finishRowCfg
        (representative && !(bits.contains true))
        { data with
          input := tail
          rowReverse :=
            .wordEnd :: (bits.map .bit).reverse ++ data.rowReverse }))
      (bits.length + 1) := by
  induction bits generalizing representative data with
  | nil =>
      have step := oneStep
        (step_scanSuffix_wordEnd representative data tail inputEq)
      simpa using step
  | cons bit bits induction =>
      let nextData : TapeData :=
        { data with
          input := bits.map .bit ++ .wordEnd :: tail
          rowReverse := .bit bit :: data.rowReverse }
      have first := oneStep
        (step_scanSuffix_bit representative bit data
          (bits.map .bit ++ .wordEnd :: tail) (by simpa using inputEq))
      have rest := induction (if bit then false else representative)
        nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (bits.length + 1)
        (scanSuffixCfg representative data)
        (scanSuffixCfg (if bit then false else representative) nextData)
        (some (finishRowCfg
          ((if bit then false else representative) &&
            !(bits.contains true))
          { nextData with
            input := tail
            rowReverse :=
              .wordEnd :: (bits.map .bit).reverse ++
                nextData.rowReverse }))
        first rest
      cases bit <;>
        simpa [nextData, List.reverse_cons, List.append_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
