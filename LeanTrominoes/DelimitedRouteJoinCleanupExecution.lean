/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinCleanupSteps
import LeanTrominoes.DelimitedRouteJoinExecutionSupport

/-! # Residual-stack cleanup for delimited-route joining -/

noncomputable section

namespace LeanTrominoes.DelimitedRouteJoin

open StateTransition Turing

def cleanupPrefixes_evalsInTime (prefixes : List Token)
    (data : TapeData) (prefixEq : data.prefixes = prefixes) :
    EvalsToInTime machine.step (cleanupPrefixesCfg data)
      (some (cleanupSuffixesCfg { data with prefixes := [] }))
      (prefixes.length + 1) := by
  induction prefixes generalizing data with
  | nil =>
      have step := step_cleanupPrefixes_nil data prefixEq
      simpa using oneStep step
  | cons token prefixes induction =>
      have first := oneStep
        (step_cleanupPrefixes_cons data token prefixes prefixEq)
      let nextData : TapeData := { data with prefixes := prefixes }
      have rest := induction nextData rfl
      have whole := EvalsToInTime.trans machine.step
        1 (prefixes.length + 1) _ _ _ first rest
      simpa [nextData, Nat.add_assoc, Nat.add_comm] using whole

def cleanupSuffixes_evalsInTime (suffixes : List Token)
    (data : TapeData) (suffixEq : data.suffixes = suffixes) :
    EvalsToInTime machine.step (cleanupSuffixesCfg data)
      (some (reverseOutputCfg { data with suffixes := [] }))
      (suffixes.length + 1) := by
  induction suffixes generalizing data with
  | nil =>
      have step := step_cleanupSuffixes_nil data suffixEq
      simpa using oneStep step
  | cons token suffixes induction =>
      have first := oneStep
        (step_cleanupSuffixes_cons data token suffixes suffixEq)
      let nextData : TapeData := { data with suffixes := suffixes }
      have rest := induction nextData rfl
      have whole := EvalsToInTime.trans machine.step
        1 (suffixes.length + 1) _ _ _ first rest
      simpa [nextData, Nat.add_assoc, Nat.add_comm] using whole

end LeanTrominoes.DelimitedRouteJoin

end
