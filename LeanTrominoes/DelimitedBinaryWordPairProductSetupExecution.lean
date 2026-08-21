/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductCopyExecution

/-! # Complete setup of the binary-word ordered product -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def setupTime (tokens : List WordToken) : Nat :=
  2 * tokens.length + 2

def setup_evalsInTime (tokens : List WordToken) :
    EvalsToInTime (TM2.step program)
      (copyInputCfg
        ⟨tokens, [], [], [], [], [], [], [], []⟩)
      (some (scanOuterCfg
        ⟨[], [], tokens, tokens, [], [], [], [], []⟩))
      (setupTime tokens) := by
  let initial : TapeData :=
    ⟨tokens, [], [], [], [], [], [], [], []⟩
  let copied : TapeData :=
    ⟨[], tokens.reverse, [], [], [], [], [], [], []⟩
  have copyRun := copyInput_evalsInTime tokens initial rfl
  have duplicateRun := duplicate_evalsInTime tokens.reverse copied rfl
  have composed := EvalsToInTime.trans (TM2.step program)
    (tokens.length + 1) (tokens.reverse.length + 1)
    (copyInputCfg initial) (duplicateCfg copied)
    (some (scanOuterCfg
      ⟨[], [], tokens, tokens, [], [], [], [], []⟩))
    (by simpa [initial, copied] using copyRun)
    (by simpa [copied] using duplicateRun)
  convert composed using 1
  simp [setupTime]
  omega

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
