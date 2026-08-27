/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRoutedRequestCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceRoutedRequestData
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ListAppendClosure

/-! # Compiler for compact routed horizontal typed-incidence requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalTypedIncidenceRoutedRequest

open Computability Turing

local instance : Inhabited AxisDirection := ⟨.invalid⟩

def finiteBlock : Token → List AxisDirection
  | .finite query => HorizontalFiniteIncidenceDirectionQuery.directions query
  | .occurrence _ => []

def occurrenceBlock : Token → List HorizontalOccurrenceRoutedRequest.Token
  | .occurrence token => [token]
  | .finite _ => []

def finiteDirections (input : List Token) : List AxisDirection :=
  input.flatMap finiteBlock

def occurrenceTokens (input : List Token) :
    List HorizontalOccurrenceRoutedRequest.Token :=
  input.flatMap occurrenceBlock

def occurrenceDirections (input : List Token) : List AxisDirection :=
  HorizontalOccurrenceRoutedRequest.output (occurrenceTokens input)

/-- Mathematical output: finite prefix first, followed by the optional routed
occurrence word. -/
def output (input : List Token) : List AxisDirection :=
  finiteDirections input ++ occurrenceDirections input

noncomputable def finiteDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id finiteDirections := by
  change TM2ComputableInPolyTime id id
    (fun input : List Token => input.flatMap finiteBlock)
  exact FiniteBlockTransducer.computableInPolyTime finiteBlock

noncomputable def occurrenceTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id occurrenceTokens := by
  change TM2ComputableInPolyTime id id
    (fun input : List Token => input.flatMap occurrenceBlock)
  exact FiniteBlockTransducer.computableInPolyTime occurrenceBlock

noncomputable def occurrenceDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id occurrenceDirections := by
  let complete := TM2CompositionMachine.computableInPolyTime
    occurrenceTokensComputableInPolyTime
    HorizontalOccurrenceRoutedRequest.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => HorizontalOccurrenceRoutedRequest.output
      (occurrenceTokens input))
  exact complete

/-- The finite and routed branches compile independently and concatenate in
their semantic order. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  change TM2ComputableInPolyTime id id
    (fun input => finiteDirections input ++ occurrenceDirections input)
  exact TM2ListAppend.computableInPolyTime
    finiteDirectionsComputableInPolyTime
    occurrenceDirectionsComputableInPolyTime

/-- Explicit compact routed request for one classified typed incidence. -/
def blockTokens : HorizontalTypedIncidenceDirectionBlock → List Token
  | .variable input .local =>
      [.finite (horizontalVariableIncidencePrefixDirectionQuery
        (horizontalVariableRoutePrefixQueryComputed input))]
  | .variable input (.routed route) =>
      .finite (horizontalVariableIncidencePrefixDirectionQuery
          (horizontalVariableRoutePrefixQueryComputed input)) ::
        (HorizontalOccurrenceRoutedRequest.semanticTokens
          (horizontalVariableOccurrenceRouteQueryComputed input)
          route).map .occurrence
  | .clause input =>
      [.finite (horizontalClauseIncidenceDirectionQuery input)]

/-- Every classified typed incidence compiles to its exact complete direction
word without first materializing the routed source geometry. -/
@[simp] theorem output_blockTokens
    (block : HorizontalTypedIncidenceDirectionBlock) :
    output (blockTokens block) = block.directions := by
  cases block with
  | «variable» input incidence =>
      cases incidence with
      | «local» =>
          simp [output, blockTokens, finiteDirections, occurrenceDirections,
            occurrenceTokens, finiteBlock, occurrenceBlock,
            HorizontalTypedIncidenceDirectionBlock.directions,
            horizontalVariableTypedIncidenceDirections,
            horizontalVariableIncidencePrefixDirectionQuery,
            HorizontalFiniteIncidenceDirectionQuery.directions_variable_input]
      | routed route =>
          simp [output, blockTokens, finiteDirections, occurrenceDirections,
            occurrenceTokens, finiteBlock, occurrenceBlock,
            HorizontalTypedIncidenceDirectionBlock.directions,
            horizontalVariableTypedIncidenceDirections,
            horizontalVariableIncidencePrefixDirectionQuery,
            HorizontalFiniteIncidenceDirectionQuery.directions_variable_input,
            HorizontalOccurrenceRoutedRequest.output_semanticTokens,
            List.flatMap_map]
  | clause input =>
      simp [output, blockTokens, finiteDirections, occurrenceDirections,
        occurrenceTokens, finiteBlock, occurrenceBlock,
        HorizontalTypedIncidenceDirectionBlock.directions,
        horizontalClauseIncidenceDirectionQuery,
        HorizontalFiniteIncidenceDirectionQuery.directions_clause_input]

abbrev NormalizedToken :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken

def normalizedOutput (input : List Token) : List NormalizedToken :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.Finalizer.output
    (output input)

@[simp] theorem normalizedOutput_blockTokens
    (block : HorizontalTypedIncidenceDirectionBlock) :
    normalizedOutput (blockTokens block) =
      block.directions.map .direction ++ [.routeEnd] := by
  unfold normalizedOutput
  rw [PeriodicThreeDM.NormalizationDirectionRequest.Batch.Finalizer.output_eq,
    output_blockTokens]

noncomputable def normalizedOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id normalizedOutput := by
  let complete := TM2CompositionMachine.computableInPolyTime
    computableInPolyTime
    PeriodicThreeDM.NormalizationDirectionRequest.Batch.Finalizer.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input =>
      PeriodicThreeDM.NormalizationDirectionRequest.Batch.Finalizer.output
        (output input))
  exact complete

end HorizontalTypedIncidenceRoutedRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
