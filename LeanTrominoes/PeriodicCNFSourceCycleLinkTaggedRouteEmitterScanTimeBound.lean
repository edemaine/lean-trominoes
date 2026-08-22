/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterScanBudget

/-! # Quadratic tagged cycle-link scan bound -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

theorem scanTime_le (input : SourceCycleLinkTaggedRouteEmitter.Input)
    (linkIndex : Nat) (tags : List Tag) (targets : List Nat)
    (outputReverse output : List OutputToken) :
    scanTime input linkIndex tags targets outputReverse output ≤
      (tags.length + 1) *
        (56 * scanSize input linkIndex targets + 1) := by
  induction tags generalizing linkIndex targets outputReverse with
  | nil =>
      simp only [scanTime, List.length_nil, zero_add, one_mul]
      simp only [scanSize]
      omega
  | cons tag tags induction =>
      cases targets with
      | nil =>
          simp only [scanTime, List.length_cons]
          simp only [scanSize]
          nlinarith
      | cons target targets =>
          let nextReverse :=
            (SourceCycleLinkTaggedRouteEmitter.linkTokens input linkIndex
              target tag).reverse ++ outputReverse
          have rest := induction (linkIndex := linkIndex + 1)
            (targets := targets) (outputReverse := nextReverse)
          have sizeLe := scanSize_next_le input linkIndex target targets
          have factorLe :
              56 * scanSize input (linkIndex + 1) targets + 1 ≤
                56 * scanSize input linkIndex (target :: targets) + 1 := by
            omega
          have scaled := Nat.mul_le_mul_left (tags.length + 1) factorLe
          have linkLe := linkTime_scanTapeData_le input linkIndex target
            tags targets outputReverse output tag
          have costLe :
              linkTime
                  (scanTapeData input linkIndex tags (target :: targets)
                    outputReverse output)
                  target (UnaryFieldEncoderMachine.unaryFields targets) tag +
                    1 ≤
                56 * scanSize input linkIndex (target :: targets) + 1 := by
            omega
          calc
            scanTime input linkIndex (tag :: tags) (target :: targets)
                outputReverse output =
              scanTime input (linkIndex + 1) tags targets
                  nextReverse output +
                (linkTime
                    (scanTapeData input linkIndex tags (target :: targets)
                      outputReverse output)
                    target (UnaryFieldEncoderMachine.unaryFields targets)
                      tag + 1) := rfl
            _ ≤ (tags.length + 1) *
                  (56 * scanSize input (linkIndex + 1) targets + 1) +
                (linkTime
                    (scanTapeData input linkIndex tags (target :: targets)
                      outputReverse output)
                    target (UnaryFieldEncoderMachine.unaryFields targets)
                      tag + 1) := Nat.add_le_add_right rest _
            _ ≤ (tags.length + 1) *
                  (56 * scanSize input linkIndex (target :: targets) + 1) +
                (56 * scanSize input linkIndex (target :: targets) + 1) :=
              Nat.add_le_add scaled costLe
            _ = ((tag :: tags).length + 1) *
                (56 * scanSize input linkIndex (target :: targets) + 1) := by
              simp only [List.length_cons]
              ring

theorem initial_scanTime_le
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    scanTime input 0 input.tags input.targets [] [] ≤
      57 * (SourceCycleLinkTaggedRouteEmitter.encode input).length ^ 2 := by
  let inputLength := (SourceCycleLinkTaggedRouteEmitter.encode input).length
  have timeLe := scanTime_le input 0 input.tags input.targets [] []
  have tagLe := literalCount_add_one_le_encode_length input
  have sizeLe := initial_scanSize_le input
  have oneLe := one_le_encode_length input
  have factorLe : 56 * scanSize input 0 input.targets + 1 ≤
      57 * inputLength := by
    dsimp only [inputLength]
    omega
  have productLe := Nat.mul_le_mul tagLe factorLe
  calc
    scanTime input 0 input.tags input.targets [] [] ≤
        (input.tags.length + 1) *
          (56 * scanSize input 0 input.targets + 1) := timeLe
    _ ≤ inputLength * (57 * inputLength) := by
      simpa only [SourceCycleLinkTaggedRouteEmitter.Input.literalCount]
        using productLe
    _ = 57 * inputLength ^ 2 := by ring

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
