/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineDirectionStreamCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler
import LeanTrominoes.SeparatedBooleanGuardCompiler
import LeanTrominoes.TM2ForkMachineTime

/-! # Delimited affine direction streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags
open PeriodicThreeDM.NormalizationDirectionRequest

/-- Emit one delimited direction block exactly when a tagged descriptor pair
is diagonal.  Shape selection remains inside `diagonalDirectionWord`. -/
def diagonalDirectionBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List Batch.NormalizedToken :=
  SeparatedBooleanGuard.guarded
    (carrierSegmentSameEdgeIndex.evalTokens tokens,
      Batch.Finalizer.output (diagonalDirectionWord tokens))

/-- The diagonal test, dynamic affine direction selector, and trailing route
delimiter form one polynomial-time pair-block compiler. -/
noncomputable def diagonalDirectionBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id diagonalDirectionBlock := by
  let guard :=
    carrierSegmentSameEdgeIndex.evalTokensComputableInPolyTime
  let directions := diagonalDirectionWordComputableInPolyTime
  let delimited := TM2CompositionMachine.computableInPolyTime directions
    Batch.Finalizer.computableInPolyTime
  let paired := TM2ForkMachine.computableInPolyTime guard delimited
  let complete := TM2CompositionMachine.computableInPolyTime paired
    (SeparatedBooleanGuard.computableInPolyTime
      (Symbol := Batch.NormalizedToken))
  change TM2ComputableInPolyTime id id
    (fun tokens => SeparatedBooleanGuard.guarded
      (carrierSegmentSameEdgeIndex.evalTokens tokens,
        Batch.Finalizer.output (diagonalDirectionWord tokens)))
  exact complete

/-- A canonical off-diagonal pair contributes no direction block or route
delimiter. -/
@[simp] theorem diagonalDirectionBlock_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    diagonalDirectionBlock (descriptorPairTokens pair) = [] := by
  unfold diagonalDirectionBlock
  rw [Predicate.evalTokens_descriptorPairTokens,
    carrierSegmentSameEdgeIndex_evalPair]
  simp [SeparatedBooleanGuard.guarded, edgeIndexNe]

/-- A listed numeric descriptor's diagonal pair contributes its complete raw
direction word followed by exactly one route delimiter. -/
theorem diagonalDirectionBlock_numeric_diagonal
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (descriptor : RouteDescriptor)
    (descriptorMember :
      descriptor ∈ PeriodicCNF.numericRouteDescriptors formula) :
    diagonalDirectionBlock
        (descriptorPairTokens (descriptor, descriptor)) =
      (Gadget.unitSubdivisionDirections descriptor.route).map
          Batch.NormalizedToken.direction ++
        [.routeEnd] := by
  unfold diagonalDirectionBlock
  rw [Predicate.evalTokens_descriptorPairTokens,
    carrierSegmentSameEdgeIndex_evalPair]
  simp [SeparatedBooleanGuard.guarded]
  exact congrArg (List.map Batch.NormalizedToken.direction)
    (diagonalDirectionWord_numeric_diagonal
      formula wellFormed degree isLocal forward descriptor descriptorMember)

/-- Apply the delimited diagonal selector independently to every complete
descriptor-pair block. -/
def diagonalDelimitedDirectionStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List Batch.NormalizedToken :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    diagonalDirectionBlock tokens

noncomputable def diagonalDelimitedDirectionStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id diagonalDelimitedDirectionStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    diagonalDirectionBlockComputableInPolyTime isPairEnd

@[simp] theorem diagonalDelimitedDirectionStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    diagonalDelimitedDirectionStream (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        diagonalDirectionBlock (descriptorPairTokens pair) := by
  exact mappedOutput_encodeDescriptorPairs diagonalDirectionBlock pairs

/-- On the numeric descriptor square, exactly one delimited raw direction
block is emitted per descriptor, in descriptor order. -/
theorem diagonalDelimitedDirectionStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    diagonalDelimitedDirectionStream
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        (Gadget.unitSubdivisionDirections descriptor.route).map
            Batch.NormalizedToken.direction ++
          [.routeEnd] := by
  rw [diagonalDelimitedDirectionStream_encodeDescriptorPairs]
  rw [PeriodicCNF.numericRouteDescriptorSquare_flatMap_diagonal_of_offDiagonal
    formula
    (fun pair => diagonalDirectionBlock (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    exact diagonalDirectionBlock_numeric_diagonal
      formula wellFormed degree isLocal forward descriptor descriptorMember
  · intro first _firstMember second _secondMember edgeIndexNe
    exact diagonalDirectionBlock_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
