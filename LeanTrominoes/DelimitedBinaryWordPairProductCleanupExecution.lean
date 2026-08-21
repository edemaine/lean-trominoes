/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductCleanupSteps

/-! # Cleanup executions for the binary-word ordered-product machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def restoreSource_evalsInTime (tokens : List WordToken) (data : TapeData)
    (sourceRestoreEq : data.sourceRestore = tokens) :
    EvalsToInTime (TM2.step program) (restoreSourceCfg data)
      (some (clearFirstCfg
        { data with
          source := tokens.reverse ++ data.source
          sourceRestore := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreSource_nil data sourceRestoreEq)
      convert step using 1 <;> simp
  | cons token tokens induction =>
      let nextData :=
        { data with
          source := token :: data.source
          sourceRestore := tokens }
      have first := oneStep
        (step_restoreSource_cons data token tokens sourceRestoreEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (restoreSourceCfg data) (restoreSourceCfg nextData)
        (some (clearFirstCfg
          { nextData with
            source := tokens.reverse ++ nextData.source
            sourceRestore := [] }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def clearFirst_evalsInTime (bits : List Bool) (data : TapeData)
    (firstOriginalEq : data.firstOriginal = bits) :
    EvalsToInTime (TM2.step program) (clearFirstCfg data)
      (some (scanOuterCfg { data with firstOriginal := [] }))
      (bits.length + 1) := by
  induction bits generalizing data with
  | nil =>
      have step := oneStep
        (step_clearFirst_nil data firstOriginalEq)
      simpa using step
  | cons bit bits induction =>
      let nextData := { data with firstOriginal := bits }
      have first := oneStep
        (step_clearFirst_cons data bit bits firstOriginalEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (bits.length + 1)
        (clearFirstCfg data) (clearFirstCfg nextData)
        (some (scanOuterCfg { nextData with firstOriginal := [] }))
        first rest
      simpa using composed

def clearSource_evalsInTime (tokens : List WordToken) (data : TapeData)
    (sourceEq : data.source = tokens) :
    EvalsToInTime (TM2.step program) (clearSourceCfg data)
      (some (reverseOutputCfg { data with source := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_clearSource_nil data sourceEq)
      simpa using step
  | cons token tokens induction =>
      let nextData := { data with source := tokens }
      have first := oneStep
        (step_clearSource_cons data token tokens sourceEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (clearSourceCfg data) (clearSourceCfg nextData)
        (some (reverseOutputCfg { nextData with source := [] }))
        first rest
      simpa using composed

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
