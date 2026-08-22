/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInputSizeBounds
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterLinkTimeBound

/-! # A monotone budget for tagged cycle-link scanning -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def scanSize (input : SourceCycleLinkTaggedRouteEmitter.Input)
    (linkIndex : Nat) (targets : List Nat) : Nat :=
  input.clauseCount + input.literalCount + linkIndex +
    (UnaryFieldEncoderMachine.unaryFields targets).length + 1

theorem scanSize_next_le (input : SourceCycleLinkTaggedRouteEmitter.Input)
    (linkIndex target : Nat) (targets : List Nat) :
    scanSize input (linkIndex + 1) targets ≤
      scanSize input linkIndex (target :: targets) := by
  simp only [scanSize, UnaryFieldEncoderMachine.unaryFields_cons,
    List.length_append, UnaryFieldEncoderMachine.unaryField_length]
  omega

theorem initial_scanSize_le
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    scanSize input 0 input.targets ≤
      (SourceCycleLinkTaggedRouteEmitter.encode input).length := by
  rw [encode_length]
  simp only [scanSize]
  omega

theorem linkTime_scanTapeData_le
    (input : SourceCycleLinkTaggedRouteEmitter.Input)
    (linkIndex target : Nat) (tags : List Tag) (targets : List Nat)
    (outputReverse output : List OutputToken) (tag : Tag) :
    linkTime
        (scanTapeData input linkIndex tags (target :: targets)
          outputReverse output)
        target (UnaryFieldEncoderMachine.unaryFields targets) tag ≤
      56 * scanSize input linkIndex (target :: targets) := by
  rw [linkTime_scanTapeData_eq]
  have targetLe := target_le_unaryFields_cons_length target targets
  simp only [scanSize]
  omega

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
