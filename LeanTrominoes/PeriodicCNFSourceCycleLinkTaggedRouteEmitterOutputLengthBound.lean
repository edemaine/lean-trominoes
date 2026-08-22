/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterScanBudget

/-! # Quadratic output bound for tagged cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

theorem linkTokens_length_le
    (input : SourceCycleLinkTaggedRouteEmitter.Input)
    (linkIndex target : Nat) (tag : Tag) (targets : List Nat) :
    (SourceCycleLinkTaggedRouteEmitter.linkTokens input linkIndex
      target tag).length ≤
        30 * scanSize input linkIndex (target :: targets) := by
  have targetLe := target_le_unaryFields_cons_length target targets
  cases tag <;>
    simp [SourceCycleLinkTaggedRouteEmitter.linkTokens,
      SourceCycleLinkTaggedRouteEmitter.sourceFields,
      SourceCycleLinkTaggedRouteEmitter.targetFields,
      CountedUnaryFieldTokens.countedFieldBlock,
      CountedUnaryFieldTokens.fields, CountedUnaryFieldTokens.field,
      PeriodicCNF.UnaryProgramTokens.atomTokens,
      SourceCycleLinkPositionTags.sourceTargetPortRank,
      SourceCycleLinkPositionTags.targetTargetPortRank,
      scanSize] <;>
    omega

theorem emitAux_length_le
    (input : SourceCycleLinkTaggedRouteEmitter.Input)
    (linkIndex : Nat) (tags : List Tag) (targets : List Nat) :
    (SourceCycleLinkTaggedRouteEmitter.emitAux input linkIndex
      tags targets).length ≤
        tags.length * (30 * scanSize input linkIndex targets) := by
  induction tags generalizing linkIndex targets with
  | nil => simp [SourceCycleLinkTaggedRouteEmitter.emitAux]
  | cons tag tags induction =>
      cases targets with
      | nil => simp [SourceCycleLinkTaggedRouteEmitter.emitAux]
      | cons target targets =>
          have linkLe := linkTokens_length_le input linkIndex target tag
            targets
          have rest := induction (linkIndex := linkIndex + 1)
            (targets := targets)
          have sizeLe := scanSize_next_le input linkIndex target targets
          have scaledSize := Nat.mul_le_mul_left 30 sizeLe
          have scaledRest := Nat.mul_le_mul_left tags.length scaledSize
          calc
            (SourceCycleLinkTaggedRouteEmitter.emitAux input linkIndex
                (tag :: tags) (target :: targets)).length =
              (SourceCycleLinkTaggedRouteEmitter.linkTokens input linkIndex
                  target tag).length +
                (SourceCycleLinkTaggedRouteEmitter.emitAux input
                  (linkIndex + 1) tags targets).length := by
                    simp only [SourceCycleLinkTaggedRouteEmitter.emitAux,
                      List.length_append]
            _ ≤ 30 * scanSize input linkIndex (target :: targets) +
                tags.length *
                  (30 * scanSize input (linkIndex + 1) targets) :=
              Nat.add_le_add linkLe rest
            _ ≤ 30 * scanSize input linkIndex (target :: targets) +
                tags.length *
                  (30 * scanSize input linkIndex (target :: targets)) :=
              Nat.add_le_add_left scaledRest _
            _ = (tag :: tags).length *
                (30 * scanSize input linkIndex (target :: targets)) := by
              simp only [List.length_cons]
              ring

theorem emit_length_le
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    (SourceCycleLinkTaggedRouteEmitter.emit input).length ≤
      30 * (SourceCycleLinkTaggedRouteEmitter.encode input).length ^ 2 := by
  let inputLength := (SourceCycleLinkTaggedRouteEmitter.encode input).length
  have outputLe := emitAux_length_le input 0 input.tags input.targets
  have tagLe := literalCount_add_one_le_encode_length input
  have sizeLe := initial_scanSize_le input
  have scaledSize := Nat.mul_le_mul_left 30 sizeLe
  have tagLe' : input.tags.length ≤ inputLength := by
    dsimp only [inputLength]
    simp only [SourceCycleLinkTaggedRouteEmitter.Input.literalCount] at tagLe
    omega
  have productLe := Nat.mul_le_mul tagLe' scaledSize
  calc
    (SourceCycleLinkTaggedRouteEmitter.emit input).length =
        (SourceCycleLinkTaggedRouteEmitter.emitAux input 0
          input.tags input.targets).length := rfl
    _ ≤ input.tags.length * (30 * scanSize input 0 input.targets) :=
      outputLe
    _ ≤ inputLength * (30 * inputLength) := productLe
    _ = 30 * inputLength ^ 2 := by ring

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
