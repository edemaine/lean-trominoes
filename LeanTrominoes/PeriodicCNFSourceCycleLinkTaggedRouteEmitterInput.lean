/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CountedUnaryFieldTokens
import LeanTrominoes.PeriodicCNFSourceCycleLinkPositionTags
import LeanTrominoes.SeparatedProductEncoding

/-! # Prepared tagged inputs for source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitter

abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol
abbrev Tag := SourceCycleLinkPositionTags.Tag
abbrev HeaderSymbol := SeparatedProductEncoding.Token UnarySymbol Tag
abbrev InputSymbol :=
  SeparatedProductEncoding.Token HeaderSymbol UnarySymbol

/-- One clause count, one finite boundary tag per link, and one unary source
target index per link. -/
structure Input where
  clauseCount : Nat
  tags : List Tag
  targets : List Nat
  valid : tags.length = targets.length

def encode (input : Input) : List InputSymbol :=
  SeparatedProductEncoding.encode
    (SeparatedProductEncoding.encode
      UnaryFieldEncoderMachine.unaryField id)
    UnaryFieldEncoderMachine.unaryFields
    ((input.clauseCount, input.tags), input.targets)

def Input.literalCount (input : Input) : Nat := input.tags.length

def sourceFields (input : Input) (linkIndex target : Nat) (tag : Tag) :
    List Nat :=
  [input.clauseCount + 2 * input.literalCount,
    3 * input.literalCount,
    input.literalCount + 2 * linkIndex,
    input.literalCount + input.clauseCount + linkIndex,
    target,
    0,
    SourceCycleLinkPositionTags.sourceTargetPortRank tag,
    0, 0, 0, 0]

def targetFields (input : Input) (linkIndex : Nat) (tag : Tag) :
    List Nat :=
  [input.clauseCount + 2 * input.literalCount,
    3 * input.literalCount,
    input.literalCount + 2 * linkIndex + 1,
    input.literalCount + input.clauseCount + linkIndex,
    linkIndex,
    1,
    SourceCycleLinkPositionTags.targetTargetPortRank tag,
    0, 0, 0, 0]

def linkTokens (input : Input) (linkIndex target : Nat) (tag : Tag) :
    List UnaryProgramTokens.Token :=
  CountedUnaryFieldTokens.countedFieldBlock
      (sourceFields input linkIndex target tag) ++
    CountedUnaryFieldTokens.countedFieldBlock
      (targetFields input linkIndex tag)

def emitAux (input : Input) : Nat → List Tag → List Nat →
    List UnaryProgramTokens.Token
  | _, [], _ => []
  | _, _, [] => []
  | linkIndex, tag :: tags, target :: targets =>
      linkTokens input linkIndex target tag ++
        emitAux input (linkIndex + 1) tags targets

def emit (input : Input) : List UnaryProgramTokens.Token :=
  emitAux input 0 input.tags input.targets

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitter
