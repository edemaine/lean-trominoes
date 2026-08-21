/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsScanSteps

/-! # Scanning one unary field into the cumulative sum -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

def unitSymbols (units : List Unit) : List Symbol :=
  units.map fun _ => .unit

/-- Consume a run of unary units and its following delimiter, adding one sum
marker per input unit. -/
def scanUnits_evalsInTime (units : List Unit) (tail : List Symbol)
    (data : TapeData)
    (inputEq : data.input = unitSymbols units ++ .delimiter :: tail) :
    EvalsToInTime (TM2.step program) (scanFieldCfg data)
      (some (readFieldCfg
        { data with
          input := tail
          sum := unitSymbols units.reverse ++ data.sum }))
      (units.length + 1) := by
  induction units generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_scanField_delimiter data tail (by
          simpa [unitSymbols] using inputEq))
      simpa [unitSymbols] using step
  | cons _ units induction =>
      let nextData : TapeData :=
        { data with
          input := unitSymbols units ++ .delimiter :: tail
          sum := .unit :: data.sum }
      have first := FiniteBlockTransducer.oneStep
        (step_scanField_unit data
          (unitSymbols units ++ .delimiter :: tail) (by
            simpa [unitSymbols] using inputEq))
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (units.length + 1)
        (scanFieldCfg data) (scanFieldCfg nextData)
        (some (readFieldCfg
          { nextData with
            input := tail
            sum := unitSymbols units.reverse ++ nextData.sum }))
        first rest
      convert composed using 1 <;>
        simp [nextData, unitSymbols, List.reverse_cons, List.map_append,
          List.append_assoc]

end UnaryPrefixSumsMachine
end LeanTrominoes
