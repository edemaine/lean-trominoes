/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanBudget
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanTime

/-! # Quadratic occurrence-scan time bound -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open SourceOccurrenceRouteTokens

theorem scanTime_le (base : TapeData) (state : ScanState)
    (tokens : List Token) :
    scanTime base state tokens ≤
      (tokens.length + 1) * (21 * scanSize base state tokens + 1) := by
  induction tokens generalizing state with
  | nil =>
      simp [scanTime, scanSize]
  | cons token tokens induction =>
      cases token with
      | clause arity =>
          let next := state.readClause
          have rest := induction next
          have sizeLe : scanSize base next tokens ≤
              scanSize base state (.clause arity :: tokens) :=
            scanSize_readClause_le base state arity tokens
          have factorLe : 21 * scanSize base next tokens + 1 ≤
              21 * scanSize base state (.clause arity :: tokens) + 1 := by
            omega
          have scaled := Nat.mul_le_mul_left (tokens.length + 1) factorLe
          have oneLe : 1 ≤
              21 * scanSize base state (.clause arity :: tokens) + 1 := by
            omega
          calc
            scanTime base state (.clause arity :: tokens) =
                scanTime base next tokens + 1 := rfl
            _ ≤ (tokens.length + 1) *
                  (21 * scanSize base next tokens + 1) + 1 :=
              Nat.add_le_add_right rest 1
            _ ≤ (tokens.length + 1) *
                  (21 * scanSize base state (.clause arity :: tokens) + 1) +
                (21 * scanSize base state (.clause arity :: tokens) + 1) :=
              Nat.add_le_add scaled oneLe
            _ = ((.clause arity :: tokens).length + 1) *
                (21 * scanSize base state (.clause arity :: tokens) + 1) := by
              simp only [List.length_cons]
              ring
      | literal index =>
          let next := state.readLiteral index
          have rest := induction next
          have sizeLe : scanSize base next tokens ≤
              scanSize base state (.literal index :: tokens) :=
            scanSize_readLiteral_le base state index tokens
          have factorLe : 21 * scanSize base next tokens + 1 ≤
              21 * scanSize base state (.literal index :: tokens) + 1 := by
            omega
          have scaled := Nat.mul_le_mul_left (tokens.length + 1) factorLe
          have oneLe : 1 ≤
              21 * scanSize base state (.literal index :: tokens) + 1 := by
            omega
          calc
            scanTime base state (.literal index :: tokens) =
                scanTime base next tokens + 1 := rfl
            _ ≤ (tokens.length + 1) *
                  (21 * scanSize base next tokens + 1) + 1 :=
              Nat.add_le_add_right rest 1
            _ ≤ (tokens.length + 1) *
                  (21 * scanSize base state (.literal index :: tokens) + 1) +
                (21 * scanSize base state (.literal index :: tokens) + 1) :=
              Nat.add_le_add scaled oneLe
            _ = ((.literal index :: tokens).length + 1) *
                (21 * scanSize base state (.literal index :: tokens) + 1) := by
              simp only [List.length_cons]
              ring
      | offsetNext value =>
          let next := state.readOffset base.clauseCount.length
            base.literalCount.length value
          have rest := induction next
          have sizeLe : scanSize base next tokens ≤
              scanSize base state (.offsetNext value :: tokens) :=
            scanSize_readOffset_le base state value tokens
          have factorLe : 21 * scanSize base next tokens + 1 ≤
              21 * scanSize base state (.offsetNext value :: tokens) + 1 := by
            omega
          have scaled := Nat.mul_le_mul_left (tokens.length + 1) factorLe
          have recordLe := recordTime_scanData_le base state tokens
          have costLe :
              recordTime (scanData base state tokens)
                  (state.targets.head?.getD 0) + 1 ≤
                21 * scanSize base state (.offsetNext value :: tokens) + 1 := by
            have sizeTail : scanSize base state tokens ≤
                scanSize base state (.offsetNext value :: tokens) := by
              simp [scanSize]
            omega
          calc
            scanTime base state (.offsetNext value :: tokens) =
                scanTime base next tokens +
                  (recordTime (scanData base state tokens)
                    (state.targets.head?.getD 0) + 1) := rfl
            _ ≤ (tokens.length + 1) *
                  (21 * scanSize base next tokens + 1) +
                (recordTime (scanData base state tokens)
                  (state.targets.head?.getD 0) + 1) :=
              Nat.add_le_add_right rest _
            _ ≤ (tokens.length + 1) *
                  (21 * scanSize base state (.offsetNext value :: tokens) + 1) +
                (21 * scanSize base state (.offsetNext value :: tokens) + 1) :=
              Nat.add_le_add scaled costLe
            _ = ((.offsetNext value :: tokens).length + 1) *
                (21 * scanSize base state (.offsetNext value :: tokens) + 1) := by
              simp only [List.length_cons]
              ring
      | literalEnd =>
          have rest := induction state
          have sizeLe := scanSize_literalEnd_le base state tokens
          have factorLe : 21 * scanSize base state tokens + 1 ≤
              21 * scanSize base state (.literalEnd :: tokens) + 1 := by
            omega
          have scaled := Nat.mul_le_mul_left (tokens.length + 1) factorLe
          have oneLe : 1 ≤
              21 * scanSize base state (.literalEnd :: tokens) + 1 := by
            omega
          calc
            scanTime base state (.literalEnd :: tokens) =
                scanTime base state tokens + 1 := rfl
            _ ≤ (tokens.length + 1) *
                  (21 * scanSize base state tokens + 1) + 1 :=
              Nat.add_le_add_right rest 1
            _ ≤ (tokens.length + 1) *
                  (21 * scanSize base state (.literalEnd :: tokens) + 1) +
                (21 * scanSize base state (.literalEnd :: tokens) + 1) :=
              Nat.add_le_add scaled oneLe
            _ = ((.literalEnd :: tokens).length + 1) *
                (21 * scanSize base state (.literalEnd :: tokens) + 1) := by
              simp only [List.length_cons]
              ring

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
