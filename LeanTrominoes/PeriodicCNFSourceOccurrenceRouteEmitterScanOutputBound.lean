/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanBudget

/-! # Quadratic output-length bound for occurrence scanning -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open SourceOccurrenceRouteTokens

theorem scan_emitted_length_le (base : TapeData) (state : ScanState)
    (tokens : List Token) :
    (scan base.clauseCount.length base.literalCount.length
      state tokens).emitted.length ≤
        state.emitted.length +
          tokens.length * (15 * scanSize base state tokens) := by
  induction tokens generalizing state with
  | nil =>
      simp [scan]
  | cons token tokens induction =>
      cases token with
      | clause arity =>
          let next := state.readClause
          have rest := induction next
          have rest' :
              (scan base.clauseCount.length base.literalCount.length
                next tokens).emitted.length ≤
                state.emitted.length +
                  tokens.length * (15 * scanSize base next tokens) := by
            simpa [next, ScanState.readClause] using rest
          have sizeLe := scanSize_readClause_le base state arity tokens
          have factorLe : 15 * scanSize base next tokens ≤
              15 * scanSize base state (.clause arity :: tokens) := by
            exact Nat.mul_le_mul_left 15 (by simpa [next] using sizeLe)
          have scaled := Nat.mul_le_mul_left tokens.length factorLe
          have stepScaled : tokens.length *
                (15 * scanSize base state (.clause arity :: tokens)) ≤
              (tokens.length + 1) *
                (15 * scanSize base state (.clause arity :: tokens)) :=
            Nat.mul_le_mul_right _ (Nat.le_succ tokens.length)
          calc
            (scan base.clauseCount.length base.literalCount.length state
                (.clause arity :: tokens)).emitted.length =
              (scan base.clauseCount.length base.literalCount.length next
                tokens).emitted.length := rfl
            _ ≤ state.emitted.length +
                tokens.length * (15 * scanSize base next tokens) := rest'
            _ ≤ state.emitted.length +
                tokens.length *
                  (15 * scanSize base state (.clause arity :: tokens)) :=
              Nat.add_le_add_left scaled _
            _ ≤ state.emitted.length +
                (.clause arity :: tokens).length *
                  (15 * scanSize base state (.clause arity :: tokens)) := by
              simpa only [List.length_cons] using
                Nat.add_le_add_left stepScaled state.emitted.length
      | literal index =>
          let next := state.readLiteral index
          have rest := induction next
          have rest' :
              (scan base.clauseCount.length base.literalCount.length
                next tokens).emitted.length ≤
                state.emitted.length +
                  tokens.length * (15 * scanSize base next tokens) := by
            simpa [next, ScanState.readLiteral] using rest
          have sizeLe := scanSize_readLiteral_le base state index tokens
          have factorLe : 15 * scanSize base next tokens ≤
              15 * scanSize base state (.literal index :: tokens) := by
            exact Nat.mul_le_mul_left 15 (by simpa [next] using sizeLe)
          have scaled := Nat.mul_le_mul_left tokens.length factorLe
          have stepScaled : tokens.length *
                (15 * scanSize base state (.literal index :: tokens)) ≤
              (tokens.length + 1) *
                (15 * scanSize base state (.literal index :: tokens)) :=
            Nat.mul_le_mul_right _ (Nat.le_succ tokens.length)
          calc
            (scan base.clauseCount.length base.literalCount.length state
                (.literal index :: tokens)).emitted.length =
              (scan base.clauseCount.length base.literalCount.length next
                tokens).emitted.length := rfl
            _ ≤ state.emitted.length +
                tokens.length * (15 * scanSize base next tokens) := rest'
            _ ≤ state.emitted.length +
                tokens.length *
                  (15 * scanSize base state (.literal index :: tokens)) :=
              Nat.add_le_add_left scaled _
            _ ≤ state.emitted.length +
                (.literal index :: tokens).length *
                  (15 * scanSize base state (.literal index :: tokens)) := by
              simpa only [List.length_cons] using
                Nat.add_le_add_left stepScaled state.emitted.length
      | offsetNext value =>
          let next := state.readOffset base.clauseCount.length
            base.literalCount.length value
          let route := SourceOccurrenceRouteEmitter.routeTokens
            base.clauseCount.length base.literalCount.length
            state.clauseIndex state.edgeIndex state.cursor.literalIndex
            (state.targets.head?.getD 0) value
            (state.cursor.anchorNext.getD value)
          have rest := induction next
          have rest' :
              (scan base.clauseCount.length base.literalCount.length
                next tokens).emitted.length ≤
                state.emitted.length + route.length +
                  tokens.length * (15 * scanSize base next tokens) := by
            simpa [next, route, ScanState.readOffset, List.length_append,
              Nat.add_assoc] using rest
          have sizeLe := scanSize_readOffset_le base state value tokens
          have factorLe : 15 * scanSize base next tokens ≤
              15 * scanSize base state (.offsetNext value :: tokens) := by
            exact Nat.mul_le_mul_left 15 (by simpa [next] using sizeLe)
          have scaled := Nat.mul_le_mul_left tokens.length factorLe
          have routeLe : route.length ≤
              15 * scanSize base state (.offsetNext value :: tokens) := by
            simpa only [route] using
              routeTokens_state_length_le base state
                (.offsetNext value :: tokens) value
          have parts := Nat.add_le_add routeLe scaled
          calc
            (scan base.clauseCount.length base.literalCount.length state
                (.offsetNext value :: tokens)).emitted.length =
              (scan base.clauseCount.length base.literalCount.length next
                tokens).emitted.length := rfl
            _ ≤ state.emitted.length + route.length +
                tokens.length * (15 * scanSize base next tokens) := rest'
            _ ≤ state.emitted.length +
                (15 * scanSize base state (.offsetNext value :: tokens) +
                  tokens.length *
                    (15 * scanSize base state (.offsetNext value :: tokens))) := by
              simpa only [Nat.add_assoc] using
                Nat.add_le_add_left parts state.emitted.length
            _ = state.emitted.length +
                (.offsetNext value :: tokens).length *
                  (15 * scanSize base state (.offsetNext value :: tokens)) := by
              simp only [List.length_cons]
              ring
      | literalEnd =>
          have rest := induction state
          have sizeLe := scanSize_literalEnd_le base state tokens
          have factorLe : 15 * scanSize base state tokens ≤
              15 * scanSize base state (.literalEnd :: tokens) := by
            omega
          have scaled := Nat.mul_le_mul_left tokens.length factorLe
          have stepScaled : tokens.length *
                (15 * scanSize base state (.literalEnd :: tokens)) ≤
              (tokens.length + 1) *
                (15 * scanSize base state (.literalEnd :: tokens)) :=
            Nat.mul_le_mul_right _ (Nat.le_succ tokens.length)
          calc
            (scan base.clauseCount.length base.literalCount.length state
                (.literalEnd :: tokens)).emitted.length =
              (scan base.clauseCount.length base.literalCount.length state
                tokens).emitted.length := rfl
            _ ≤ state.emitted.length +
                tokens.length * (15 * scanSize base state tokens) := rest
            _ ≤ state.emitted.length +
                tokens.length *
                  (15 * scanSize base state (.literalEnd :: tokens)) :=
              Nat.add_le_add_left scaled _
            _ ≤ state.emitted.length +
                (.literalEnd :: tokens).length *
                  (15 * scanSize base state (.literalEnd :: tokens)) := by
              simpa only [List.length_cons] using
                Nat.add_le_add_left stepScaled state.emitted.length

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
