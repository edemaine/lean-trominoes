/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinCompiler
import LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookupCompiler
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicThreeDMContractedDirectionAssemblerBatchCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Keyed contraction of independently compiled incidence directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace KeyedContractedIncidence

open Computability Turing
open PeriodicThreeDM

abbrev DirectionToken :=
  FiniteAlphabetDelimitedBlockJoin.Token AxisDirection

abbrev JoinedToken :=
  FiniteAlphabetDelimitedBlockJoin.Token
    ContractedDirectionAssembler.Token

/-- One independently delimited role block for every requested incidence. -/
def roleBlock (role : ContractedDirectionAssembler.Role) :
    List JoinedToken :=
  [.value (.role role), .blockEnd]

def roleTokens (roles : List ContractedDirectionAssembler.Role) :
    List JoinedToken :=
  roles.flatMap roleBlock

/-- Reinterpret a selected direction token in the assembler's payload
alphabet while preserving its incidence delimiter. -/
def directionBlock : DirectionToken → List JoinedToken
  | .value direction => [.value (.direction direction)]
  | .blockEnd => [.blockEnd]

def directionTokens (tokens : List DirectionToken) : List JoinedToken :=
  tokens.flatMap directionBlock

/-- Erase the generic outer delimiter in favor of the contracted assembler's
incidence delimiter. -/
def assemblerBlock : JoinedToken →
    List ContractedDirectionAssembler.Token
  | .value token => [token]
  | .blockEnd => [.incidenceEnd]

def assemblerTokens (tokens : List JoinedToken) :
    List ContractedDirectionAssembler.Token :=
  tokens.flatMap assemblerBlock

/-- Select canonical incidence blocks by arbitrary keys, prepend their
aligned contraction roles, and expose the exact assembler input stream. -/
noncomputable def inputTokens
    (queries : List Nat)
    (roles : List ContractedDirectionAssembler.Role)
    (blockKeys : List Nat)
    (incidences : List DirectionToken) :
    List ContractedDirectionAssembler.Token :=
  assemblerTokens <|
    FiniteAlphabetDelimitedBlockJoin.joined
      (roleTokens roles)
      (directionTokens <|
        FiniteAlphabetKeyedDelimitedBlockLookup.selected
          queries blockKeys incidences)

/-- Run the established independently delimited contracted assembler after
keyed incidence selection and role alignment. -/
noncomputable def output
    (queries : List Nat)
    (roles : List ContractedDirectionAssembler.Role)
    (blockKeys : List Nat)
    (incidences : List DirectionToken) :
    List NormalizationDirectionRequest.Batch.NormalizedToken :=
  ContractedDirectionAssembler.output
    (inputTokens queries roles blockKeys incidences)

noncomputable def roleTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id roleTokens :=
  FiniteBlockTransducer.computableInPolyTime roleBlock

noncomputable def directionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id directionTokens :=
  FiniteBlockTransducer.computableInPolyTime directionBlock

noncomputable def assemblerTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id assemblerTokens :=
  FiniteBlockTransducer.computableInPolyTime assemblerBlock

/-- Any polynomial-time query, role-code, block-key, and delimited-incidence
compilers compose to the keyed contracted assembler input. -/
noncomputable def inputTokensComputableInPolyTimeOf
    {Source SourceSymbol : Type}
    [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol)
    (queries blockKeys : Source → List Nat)
    (roles : Source → List ContractedDirectionAssembler.Role)
    (incidences : Source → List DirectionToken)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (roleCompiler : TM2ComputableInPolyTime encodeSource id roles)
    (blockKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields blockKeys)
    (incidenceCompiler : TM2ComputableInPolyTime encodeSource id incidences) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => inputTokens
        (queries source) (roles source) (blockKeys source)
        (incidences source)) := by
  let selectedCompiler :=
    FiniteAlphabetKeyedDelimitedBlockLookup.selectedComputableInPolyTimeOf
      encodeSource queries blockKeys incidences
      queryCompiler blockKeyCompiler incidenceCompiler
  let convertedDirections := TM2CompositionMachine.computableInPolyTime
    selectedCompiler directionTokensComputableInPolyTime
  let delimitedRoles := TM2CompositionMachine.computableInPolyTime
    roleCompiler roleTokensComputableInPolyTime
  let joinedCompiler :=
    FiniteAlphabetDelimitedBlockJoin.joinedComputableInPolyTimeOf
      encodeSource
      (fun source => roleTokens (roles source))
      (fun source => directionTokens <|
        FiniteAlphabetKeyedDelimitedBlockLookup.selected
          (queries source) (blockKeys source) (incidences source))
      delimitedRoles convertedDirections
  exact TM2CompositionMachine.computableInPolyTime
    joinedCompiler assemblerTokensComputableInPolyTime

/-- The complete keyed selection, role alignment, and contracted assembly
pipeline is polynomial-time. -/
noncomputable def outputComputableInPolyTimeOf
    {Source SourceSymbol : Type}
    [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol)
    (queries blockKeys : Source → List Nat)
    (roles : Source → List ContractedDirectionAssembler.Role)
    (incidences : Source → List DirectionToken)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (roleCompiler : TM2ComputableInPolyTime encodeSource id roles)
    (blockKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields blockKeys)
    (incidenceCompiler : TM2ComputableInPolyTime encodeSource id incidences) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => output
        (queries source) (roles source) (blockKeys source)
        (incidences source)) :=
  TM2CompositionMachine.computableInPolyTime
    (inputTokensComputableInPolyTimeOf encodeSource
      queries blockKeys roles incidences queryCompiler roleCompiler
      blockKeyCompiler incidenceCompiler)
    ContractedDirectionAssembler.outputComputableInPolyTime

end KeyedContractedIncidence
end PeriodicCNFStripReduction
end LeanTrominoes

end
