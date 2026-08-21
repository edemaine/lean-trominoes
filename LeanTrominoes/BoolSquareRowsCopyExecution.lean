/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsCountSteps

/-! # Input-copy execution of the Boolean square-row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

def workTokens (bits : List Bool) : List Unit :=
  bits.reverse.map fun _ => ()

def copyInput_evalsInTime (bits : List Bool) (data : TapeData)
    (inputEq : data.input = bits) :
    EvalsToInTime (TM2.step program) (copyInputCfg data)
      (some (initOddCfg
        { data with
          input := []
          sourceReverse := bits.reverse ++ data.sourceReverse
          work := workTokens bits ++ data.work }))
      (bits.length + 1) := by
  induction bits generalizing data with
  | nil =>
      have step := oneStep (step_copyInput_nil data inputEq)
      simpa [workTokens] using step
  | cons bit bits induction =>
      let nextData : TapeData :=
        { data with
          input := bits
          sourceReverse := bit :: data.sourceReverse
          work := () :: data.work }
      have first := oneStep
        (step_copyInput_cons data bit bits inputEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (bits.length + 1)
        (copyInputCfg data) (copyInputCfg nextData)
        (some (initOddCfg
          { nextData with
            input := []
            sourceReverse := bits.reverse ++ nextData.sourceReverse
            work := workTokens bits ++ nextData.work }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc,
          workTokens, List.map_append]
      · simp

end BoolSquareRowsMachine
end LeanTrominoes
