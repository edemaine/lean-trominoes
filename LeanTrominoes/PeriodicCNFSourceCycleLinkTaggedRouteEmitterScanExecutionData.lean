/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterLinkOutputSemantics

/-! # Canonical scan configurations for tagged cycle-link emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def scanTapeData (input : SourceCycleLinkTaggedRouteEmitter.Input)
    (linkIndex : Nat) (tags : List Tag) (targets : List Nat)
    (outputReverse output : List OutputToken) : TapeData :=
  ⟨[], [], tags, [], UnaryFieldEncoderMachine.unaryFields targets,
    List.replicate input.clauseCount (),
    List.replicate input.literalCount (),
    List.replicate linkIndex (), [], outputReverse, output⟩

def finalTag : Tag → List Tag → Tag
  | cursor, [] => cursor
  | _, tag :: tags => finalTag tag tags

def scanTime (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    Nat → List Tag → List Nat → List OutputToken →
      List OutputToken → Nat
  | _, [], _, _, _ => 1
  | _, _ :: _, [], _, _ => 1
  | linkIndex, tag :: tags, target :: targets, outputReverse, output =>
      scanTime input (linkIndex + 1) tags targets
          ((SourceCycleLinkTaggedRouteEmitter.linkTokens input linkIndex
            target tag).reverse ++ outputReverse) output +
        (linkTime
          (scanTapeData input linkIndex tags (target :: targets)
            outputReverse output)
          target (UnaryFieldEncoderMachine.unaryFields targets) tag + 1)

@[simp] theorem scanTapeData_tags
    (input : SourceCycleLinkTaggedRouteEmitter.Input) (linkIndex : Nat)
    (tags : List Tag) (targets : List Nat)
    (outputReverse output : List OutputToken) :
    (scanTapeData input linkIndex tags targets outputReverse output).tags =
      tags := by
  rfl

theorem scanTapeData_target_cons
    (input : SourceCycleLinkTaggedRouteEmitter.Input) (linkIndex target : Nat)
    (tags : List Tag) (targets : List Nat)
    (outputReverse output : List OutputToken) :
    (scanTapeData input linkIndex tags (target :: targets)
      outputReverse output).targets =
      List.replicate target .unit ++ .delimiter ::
        UnaryFieldEncoderMachine.unaryFields targets := by
  simp [scanTapeData, UnaryFieldEncoderMachine.unaryFields_cons,
    UnaryFieldEncoderMachine.unaryField]

theorem afterLinkData_scanTapeData_eq
    (input : SourceCycleLinkTaggedRouteEmitter.Input)
    (linkIndex target : Nat) (tag : Tag) (tags : List Tag)
    (targets : List Nat) (outputReverse output : List OutputToken) :
    afterLinkData
        (scanTapeData input linkIndex tags (target :: targets)
          outputReverse output)
        target (UnaryFieldEncoderMachine.unaryFields targets) tag =
      scanTapeData input (linkIndex + 1) tags targets
        ((SourceCycleLinkTaggedRouteEmitter.linkTokens
          input linkIndex target tag).reverse ++ outputReverse)
        output := by
  rw [afterLinkData_eq]
  rw [emittedLinkTokens_eq_linkTokens input _ linkIndex target tag
    (by simp [scanTapeData]) (by simp [scanTapeData])
    (by simp [scanTapeData])]
  simp [scanTapeData]
  change () :: List.replicate linkIndex () =
    List.replicate (Nat.succ linkIndex) ()
  rw [List.replicate_succ]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
