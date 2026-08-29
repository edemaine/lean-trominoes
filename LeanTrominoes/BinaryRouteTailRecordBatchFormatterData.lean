/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordFormatterData

/-! # Batched formatting of binary route-tail records -/

namespace LeanTrominoes
namespace BinaryRouteTailRecordBatchFormatter

open PeriodicCNF
open PeriodicCNFStripReduction

abbrev Profile :=
  FormulaShapeDirectionOrdering.DirectedClauseProfile

abbrev SourceToken :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken

abbrev OutputToken := HorizontalRoutedRouteTailRecord.Token

/-- Finite framing around a stream of four-route binary-clause blocks. -/
inductive Token
  | firstProfile (profile : Profile)
  | secondProfile (profile : Profile)
  | source (token : SourceToken)
  deriving DecidableEq, Fintype, Inhabited

/-- Finite control stores the two profiles of the current block and delegates
the four-route scan to the established single-block formatter. -/
structure State where
  firstProfile : Profile
  secondProfile : Profile
  control : BinaryRouteTailRecordFormatter.Control
  deriving DecidableEq, Fintype

instance : Inhabited State :=
  ⟨⟨default, default, .firstHead⟩⟩

def initial : State := ⟨default, default, .firstHead⟩

def transition (state : State) : Token → State × List OutputToken
  | .firstProfile profile =>
      (⟨profile, state.secondProfile, .firstHead⟩, [])
  | .secondProfile profile =>
      (⟨state.firstProfile, profile, state.control⟩, [])
  | .source token =>
      let result := BinaryRouteTailRecordFormatter.transition
        state.firstProfile state.secondProfile state.control token
      (⟨state.firstProfile, state.secondProfile, result.1⟩, result.2)

def finish (_ : State) : List OutputToken := []

def output (input : List Token) : List OutputToken :=
  FiniteStateTransducer.output initial transition finish input

/-- One semantic input block: two clause profiles and their four complete
routes in clause-major incidence order. -/
structure Block where
  firstProfile : Profile
  secondProfile : Profile
  first : List AxisDirection
  second : List AxisDirection
  third : List AxisDirection
  fourth : List AxisDirection

def sourceTokens (directions : List AxisDirection) : List Token :=
  (PeriodicOrthocrossing.CarrierSpanRouteDirections.delimitedDirections
    directions).map Token.source

def blockTokens (block : Block) : List Token :=
  .firstProfile block.firstProfile ::
    .secondProfile block.secondProfile ::
      (sourceTokens block.first ++
        sourceTokens block.second ++
        sourceTokens block.third ++
        sourceTokens block.fourth)

def tokens (blocks : List Block) : List Token :=
  blocks.flatMap blockTokens

def Block.records (block : Block) : List OutputToken :=
  HorizontalRoutedRouteTailRecord.clauseRecord
      block.firstProfile [block.first.tail, block.second.tail] ++
    HorizontalRoutedRouteTailRecord.clauseRecord
      block.secondProfile [block.third.tail, block.fourth.tail]

def records (blocks : List Block) : List OutputToken :=
  blocks.flatMap Block.records

end BinaryRouteTailRecordBatchFormatter
end LeanTrominoes
