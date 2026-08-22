/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterOutputTapeUpdates

/-! # Output-token push algebra for tagged cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem stepAux_pushTokens (tokens : List OutputToken)
    (next : TM2.Stmt Alphabet Label State) (state : State)
    (data : TapeData) :
    TM2.stepAux (pushTokens tokens next) state (tapes data) =
      TM2.stepAux next state
        (tapes { data with
          outputReverse := tokens.reverse ++ data.outputReverse }) := by
  induction tokens generalizing data with
  | nil => simp [pushTokens]
  | cons token tokens induction =>
      simp only [pushTokens, List.foldr_cons, TM2.stepAux]
      rw [update_tapes_outputReverse]
      change TM2.stepAux (pushTokens tokens next) state
          (tapes { data with
            outputReverse := token :: data.outputReverse }) = _
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
