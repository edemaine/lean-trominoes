/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineScaledReversedDirectionStreamCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler
import LeanTrominoes.SeparatedBooleanGuardCompiler
import LeanTrominoes.TM2ForkMachineTime

/-! # Delimited doubled reversed affine direction streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags
open PeriodicThreeDM.NormalizationDirectionRequest

/-- Emit one delimited doubled reversed direction block exactly for a diagonal
descriptor pair. -/
def diagonalScaledReversedDirectionBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List Batch.NormalizedToken :=
  SeparatedBooleanGuard.guarded
    (carrierSegmentSameEdgeIndex.evalTokens tokens,
      Batch.Finalizer.output
        (diagonalScaledReversedDirectionWord tokens))

/-- The diagonal guard, dynamic doubled reversed word, and final delimiter
form a polynomial-time pair-block compiler. -/
noncomputable def
    diagonalScaledReversedDirectionBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id
      diagonalScaledReversedDirectionBlock := by
  let guard := carrierSegmentSameEdgeIndex.evalTokensComputableInPolyTime
  let directions :=
    diagonalScaledReversedDirectionWordComputableInPolyTime
  let delimited := TM2CompositionMachine.computableInPolyTime directions
    Batch.Finalizer.computableInPolyTime
  let paired := TM2ForkMachine.computableInPolyTime guard delimited
  let complete := TM2CompositionMachine.computableInPolyTime paired
    (SeparatedBooleanGuard.computableInPolyTime
      (Symbol := Batch.NormalizedToken))
  change TM2ComputableInPolyTime id id
    (fun tokens => SeparatedBooleanGuard.guarded
      (carrierSegmentSameEdgeIndex.evalTokens tokens,
        Batch.Finalizer.output
          (diagonalScaledReversedDirectionWord tokens)))
  exact complete

/-- Off-diagonal pairs contribute neither directions nor a delimiter. -/
@[simp] theorem
    diagonalScaledReversedDirectionBlock_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    diagonalScaledReversedDirectionBlock
        (descriptorPairTokens pair) = [] := by
  unfold diagonalScaledReversedDirectionBlock
  rw [Predicate.evalTokens_descriptorPairTokens,
    carrierSegmentSameEdgeIndex_evalPair]
  simp [SeparatedBooleanGuard.guarded, edgeIndexNe]

/-- A numeric diagonal contributes its complete doubled reversed route word
and exactly one boundary. -/
theorem diagonalScaledReversedDirectionBlock_numeric_diagonal
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (descriptor : RouteDescriptor)
    (descriptorMember :
      descriptor ∈ PeriodicCNF.numericRouteDescriptors formula) :
    diagonalScaledReversedDirectionBlock
        (descriptorPairTokens (descriptor, descriptor)) =
      (Gadget.unitSubdivisionDirections
          (scalePolyline 2 descriptor.route).reverse).map
          Batch.NormalizedToken.direction ++
        [.routeEnd] := by
  unfold diagonalScaledReversedDirectionBlock
  rw [Predicate.evalTokens_descriptorPairTokens,
    carrierSegmentSameEdgeIndex_evalPair]
  simp [SeparatedBooleanGuard.guarded]
  exact congrArg (List.map Batch.NormalizedToken.direction)
    (diagonalScaledReversedDirectionWord_numeric_diagonal
      formula wellFormed degree isLocal forward descriptor descriptorMember)

/-- Apply the delimited selector to every complete pair block. -/
def diagonalScaledReversedDelimitedDirectionStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List Batch.NormalizedToken :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    diagonalScaledReversedDirectionBlock tokens

noncomputable def
    diagonalScaledReversedDelimitedDirectionStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      diagonalScaledReversedDelimitedDirectionStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    diagonalScaledReversedDirectionBlockComputableInPolyTime isPairEnd

@[simp] theorem
    diagonalScaledReversedDelimitedDirectionStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    diagonalScaledReversedDelimitedDirectionStream
        (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        diagonalScaledReversedDirectionBlock
          (descriptorPairTokens pair) := by
  exact mappedOutput_encodeDescriptorPairs
    diagonalScaledReversedDirectionBlock pairs

/-- The numeric descriptor square produces one delimited doubled reversed
block per descriptor. -/
theorem
    diagonalScaledReversedDelimitedDirectionStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    diagonalScaledReversedDelimitedDirectionStream
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        (Gadget.unitSubdivisionDirections
            (scalePolyline 2 descriptor.route).reverse).map
            Batch.NormalizedToken.direction ++
          [.routeEnd] := by
  rw [diagonalScaledReversedDelimitedDirectionStream_encodeDescriptorPairs]
  rw [PeriodicCNF.numericRouteDescriptorSquare_flatMap_diagonal_of_offDiagonal
    formula
    (fun pair => diagonalScaledReversedDirectionBlock
      (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    exact diagonalScaledReversedDirectionBlock_numeric_diagonal
      formula wellFormed degree isLocal forward descriptor descriptorMember
  · intro first _ second _ edgeIndexNe
    exact diagonalScaledReversedDirectionBlock_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
