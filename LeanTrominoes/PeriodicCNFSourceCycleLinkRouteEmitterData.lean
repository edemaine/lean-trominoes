/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CountedUnaryFieldTokens
import LeanTrominoes.PeriodicCNFSourceSplitRouteDescriptorTokenData
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Semantic source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkRouteEmitter

/-- A clause count followed by the occurrence count of each distinct source
atom, in the source-variable order. -/
structure Input where
  clauseCount : Nat
  groupSizes : List Nat

abbrev InputSymbol := UnaryFieldEncoderMachine.Symbol

/-- Delimiter-separated unary encoding consumed by the cycle-link emitter. -/
def encode (input : Input) : List InputSymbol :=
  UnaryFieldEncoderMachine.unaryFields
    (input.clauseCount :: input.groupSizes)

/-- Total number of source literal occurrences. -/
def Input.literalCount (input : Input) : Nat := input.groupSizes.sum

/-- Eleven unary fields of the negative-source incidence of one cycle link.
`linkIndex` is global, while `position` is local to its atom group. -/
def sourceFields (input : Input) (groupSize linkIndex position : Nat) :
    List Nat :=
  [input.clauseCount + 2 * input.literalCount,
    3 * input.literalCount,
    input.literalCount + 2 * linkIndex,
    input.literalCount + input.clauseCount + linkIndex,
    if position = 0 then linkIndex + groupSize - 1 else linkIndex - 1,
    0,
    if position = 0 then 1 else 2,
    0, 0, 0, 0]

/-- Eleven unary fields of the positive-target incidence of one cycle link. -/
def targetFields (input : Input) (groupSize linkIndex position : Nat) :
    List Nat :=
  [input.clauseCount + 2 * input.literalCount,
    3 * input.literalCount,
    input.literalCount + 2 * linkIndex + 1,
    input.literalCount + input.clauseCount + linkIndex,
    linkIndex,
    1,
    if position + 1 = groupSize then 2 else 1,
    0, 0, 0, 0]

/-- The two counted route records belonging to one directed cycle link. -/
def linkTokens (input : Input) (groupSize linkIndex position : Nat) :
    List UnaryProgramTokens.Token :=
  CountedUnaryFieldTokens.countedFieldBlock
      (sourceFields input groupSize linkIndex position) ++
    CountedUnaryFieldTokens.countedFieldBlock
      (targetFields input groupSize linkIndex position)

/-- Emit one atom group's links, beginning at its global block start. -/
def groupTokens (input : Input) (blockStart groupSize : Nat) :
    List UnaryProgramTokens.Token :=
  (List.range groupSize).flatMap fun position =>
    linkTokens input groupSize (blockStart + position) position

/-- Emit successive atom groups while carrying the next global link index. -/
def groupsTokensAux (input : Input) : Nat → List Nat →
    List UnaryProgramTokens.Token
  | _, [] => []
  | blockStart, groupSize :: groupSizes =>
      groupTokens input blockStart groupSize ++
        groupsTokensAux input (blockStart + groupSize) groupSizes

/-- Complete counted cycle-link route stream. -/
def emit (input : Input) : List UnaryProgramTokens.Token :=
  groupsTokensAux input 0 input.groupSizes

/-- Exact semantic input prepared from a promised flat source. -/
def sourceInput (source : SourceSplitRouteDescriptorTokens.Source) : Input where
  clauseCount := source.formula.clauses.length
  groupSizes :=
    (PeriodicThreeSATThree.sourceVariables source.formula).map fun atom =>
      (PeriodicThreeSATThree.occurrenceVariables
        source.formula atom).length

end LeanTrominoes.PeriodicCNF.SourceCycleLinkRouteEmitter
