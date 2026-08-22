/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairLengthComparisonSteps

/-! # Output reversal for delimited word-length comparison -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairLengthComparisonMachine

def reverseTime (results : List LengthOrdering) : Nat := results.length + 1

def reverse_evalsInTime (results output : List LengthOrdering) :
    EvalsToInTime (TM2.step program)
      (reverseCfg ⟨[], [], [], results, output⟩)
      (some (haltCfg (results.reverse ++ output)))
      (reverseTime results) := by
  induction results generalizing output with
  | nil =>
      have step := oneStep (step_reverse_nil output)
      simpa [reverseTime] using step
  | cons result results induction =>
      have first := oneStep (step_reverse_cons
        ⟨[], [], [], result :: results, output⟩ result results rfl)
      have rest := induction (result :: output)
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (reverseTime results)
        (reverseCfg ⟨[], [], [], result :: results, output⟩)
        (reverseCfg ⟨[], [], [], results, result :: output⟩)
        (some (haltCfg (results.reverse ++ result :: output)))
        first rest
      convert composed using 1
      · simp [List.reverse_cons, List.append_assoc]
      · simp [reverseTime]

end DelimitedBinaryWordPairLengthComparisonMachine
end LeanTrominoes
