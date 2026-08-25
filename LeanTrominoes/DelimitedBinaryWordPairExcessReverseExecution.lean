/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessMachineSteps

/-! # Output reversal for unary word-pair excesses -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairExcessMachine

def reverseTime (symbols : List UnaryFieldEncoderMachine.Symbol) : Nat :=
  symbols.length + 1

def reverse_evalsInTime (keepFirst : Bool)
    (symbols output : List UnaryFieldEncoderMachine.Symbol) :
    EvalsToInTime (TM2.step (program keepFirst))
      (reverseOutputCfg ⟨[], [], [], symbols, output⟩)
      (some (haltCfg (symbols.reverse ++ output)))
      (reverseTime symbols) := by
  induction symbols generalizing output with
  | nil =>
      have step := oneStep (step_reverseOutput_nil keepFirst output)
      simpa [reverseTime] using step
  | cons symbol symbols induction =>
      have first := oneStep (step_reverseOutput_cons keepFirst
        ⟨[], [], [], symbol :: symbols, output⟩ symbol symbols rfl)
      have rest := induction (symbol :: output)
      have composed := EvalsToInTime.trans (TM2.step (program keepFirst))
        1 (reverseTime symbols)
        (reverseOutputCfg ⟨[], [], [], symbol :: symbols, output⟩)
        (reverseOutputCfg ⟨[], [], [], symbols, symbol :: output⟩)
        (some (haltCfg (symbols.reverse ++ symbol :: output)))
        first rest
      convert composed using 1
      · simp [List.reverse_cons, List.append_assoc]
      · simp [reverseTime, Nat.add_comm]

end DelimitedBinaryWordPairExcessMachine
end LeanTrominoes
