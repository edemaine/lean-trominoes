/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsCountSteps

/-! # Counter cleanup loops of the Boolean square-row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

def restoreOdd_evalsInTime (tokens : List Unit) (data : TapeData)
    (restoreEq : data.oddRestore = tokens) :
    EvalsToInTime (TM2.step program) (restoreOddCfg data)
      (some (consumeWorkCfg
        { data with
          odd := () :: () :: tokens.reverse ++ data.odd
          oddRestore := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_restoreOdd_nil data restoreEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData :=
        { data with
          odd := () :: data.odd
          oddRestore := tokens }
      have first := oneStep
        (step_restoreOdd_cons data tokens restoreEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (restoreOddCfg data) (restoreOddCfg nextData)
        (some (consumeWorkCfg
          { nextData with
            odd := () :: () :: tokens.reverse ++ nextData.odd
            oddRestore := [] }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def clearOdd_evalsInTime (tokens : List Unit) (data : TapeData)
    (oddEq : data.odd = tokens) :
    EvalsToInTime (TM2.step program) (clearOddCfg data)
      (some (clearOddRestoreCfg { data with odd := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_clearOdd_nil data oddEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData := { data with odd := tokens }
      have first := oneStep (step_clearOdd_cons data tokens oddEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (clearOddCfg data) (clearOddCfg nextData)
        (some (clearOddRestoreCfg { nextData with odd := [] }))
        first rest
      simpa [nextData] using composed

def clearOddRestore_evalsInTime (tokens : List Unit) (data : TapeData)
    (restoreEq : data.oddRestore = tokens) :
    EvalsToInTime (TM2.step program) (clearOddRestoreCfg data)
      (some (moveRootCfg { data with oddRestore := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_clearOddRestore_nil data restoreEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData := { data with oddRestore := tokens }
      have first := oneStep
        (step_clearOddRestore_cons data tokens restoreEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (clearOddRestoreCfg data) (clearOddRestoreCfg nextData)
        (some (moveRootCfg { nextData with oddRestore := [] }))
        first rest
      simpa [nextData] using composed

def moveRoot_evalsInTime (tokens : List Unit) (data : TapeData)
    (rootEq : data.root = tokens) :
    EvalsToInTime (TM2.step program) (moveRootCfg data)
      (some (reverseSourceCfg
        { data with
          root := []
          rowCountdown := tokens.reverse ++ data.rowCountdown }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_moveRoot_nil data rootEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData :=
        { data with
          root := tokens
          rowCountdown := () :: data.rowCountdown }
      have first := oneStep (step_moveRoot_cons data tokens rootEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (moveRootCfg data) (moveRootCfg nextData)
        (some (reverseSourceCfg
          { nextData with
            root := []
            rowCountdown := tokens.reverse ++ nextData.rowCountdown }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def reverseSource_evalsInTime (bits : List Bool) (data : TapeData)
    (reverseEq : data.sourceReverse = bits) :
    EvalsToInTime (TM2.step program) (reverseSourceCfg data)
      (some (startRowsCfg
        { data with
          sourceReverse := []
          source := bits.reverse ++ data.source }))
      (bits.length + 1) := by
  induction bits generalizing data with
  | nil =>
      have step := oneStep (step_reverseSource_nil data reverseEq)
      simpa using step
  | cons bit bits induction =>
      let nextData : TapeData :=
        { data with
          sourceReverse := bits
          source := bit :: data.source }
      have first := oneStep
        (step_reverseSource_cons data bit bits reverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (bits.length + 1)
        (reverseSourceCfg data) (reverseSourceCfg nextData)
        (some (startRowsCfg
          { nextData with
            sourceReverse := []
            source := bits.reverse ++ nextData.source }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end BoolSquareRowsMachine
end LeanTrominoes
