/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.ListFlatMapUniqueKey
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSegmentGeometry
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSquareDiagonal
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineGuardedDirectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineScaledReversedDirectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelectionSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Selecting doubled reversed affine route words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags

/-- Candidate doubled reversed word contributed by one diagonal shape. -/
def RouteShape.guardedScaledReversedDirectionWord
    (shape : RouteShape)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List AxisDirection :=
  if shape.diagonalDirectionGuard.evalTokens tokens then
    shape.compiledScaledReversedDirectionWord .first tokens
  else
    []

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- Each guarded doubled reversed shape remains a polynomial-time streaming
compiler. -/
noncomputable def
    RouteShape.guardedScaledReversedDirectionWordComputableInPolyTime
    (shape : RouteShape) :
    TM2ComputableInPolyTime id id
      shape.guardedScaledReversedDirectionWord := by
  let guard := shape.diagonalDirectionGuard.evalTokensComputableInPolyTime
  let word :=
    shape.compiledScaledReversedDirectionWordComputableInPolyTime .first
  let paired := TM2ForkMachine.computableInPolyTime guard word
  let gated := TM2CompositionMachine.computableInPolyTime paired
    (SeparatedBooleanGuard.computableInPolyTime
      (Symbol := AxisDirection))
  change TM2ComputableInPolyTime id id
    (fun tokens => SeparatedBooleanGuard.guarded
      (shape.diagonalDirectionGuard.evalTokens tokens,
        shape.compiledScaledReversedDirectionWord .first tokens))
  exact gated

/-- Canonical input contributes exactly when both diagonal and shape guards
hold. -/
@[simp] theorem
    RouteShape.guardedScaledReversedDirectionWord_descriptorPairTokens
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    shape.guardedScaledReversedDirectionWord
        (descriptorPairTokens pair) =
      if pair.1.edgeIndex = pair.2.edgeIndex ∧ shape.Matches pair.1 then
        shape.scaledReversedDirectionWord .first pair
      else
        [] := by
  unfold RouteShape.guardedScaledReversedDirectionWord
  rw [Predicate.evalTokens_descriptorPairTokens]
  by_cases sameEdge : pair.1.edgeIndex = pair.2.edgeIndex <;>
    by_cases shapeMatches : shape.Matches pair.1 <;>
      simp [RouteShape.diagonalDirectionGuard, evalPair_all,
        carrierSegmentSameEdgeIndex_evalPair,
        RouteShape.evalPair_guard, descriptorAt,
        sameEdge, shapeMatches]
  exact
    shape.compiledScaledReversedDirectionWord_descriptorPairTokens
      .first pair

/-- Concatenate the doubled reversed candidates of fixed shapes. -/
def guardedScaledReversedDirectionWords
    (shapes : List RouteShape)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List AxisDirection :=
  shapes.flatMap fun shape =>
    shape.guardedScaledReversedDirectionWord tokens

/-- Unique diagonal doubled reversed route word among all 28 shapes. -/
def diagonalScaledReversedDirectionWord
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List AxisDirection :=
  guardedScaledReversedDirectionWords allRouteShapes tokens

/-- A fixed candidate list can be concatenated in polynomial time. -/
noncomputable def guardedScaledReversedDirectionWordsComputableInPolyTime :
    (shapes : List RouteShape) →
      TM2ComputableInPolyTime id id
        (guardedScaledReversedDirectionWords shapes)
  | [] => by
      change TM2ComputableInPolyTime id id
        (fun _ : List RouteDescriptorPairFieldTags.Token =>
          ([] : List AxisDirection))
      let empty := FiniteBlockTransducer.computableInPolyTime
        (fun _ : RouteDescriptorPairFieldTags.Token =>
          ([] : List AxisDirection))
      exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq empty
        (fun tokens => by simp)
  | shape :: shapes => by
      let first :=
        shape.guardedScaledReversedDirectionWordComputableInPolyTime
      let rest :=
        guardedScaledReversedDirectionWordsComputableInPolyTime shapes
      change TM2ComputableInPolyTime id id
        (fun tokens =>
          shape.guardedScaledReversedDirectionWord tokens ++
            guardedScaledReversedDirectionWords shapes tokens)
      exact TM2ListAppend.computableInPolyTime first rest

/-- Complete 28-shape doubled reversed selector. -/
noncomputable def diagonalScaledReversedDirectionWordComputableInPolyTime :
    TM2ComputableInPolyTime id id
      diagonalScaledReversedDirectionWord := by
  change TM2ComputableInPolyTime id id
    (guardedScaledReversedDirectionWords allRouteShapes)
  exact guardedScaledReversedDirectionWordsComputableInPolyTime
    allRouteShapes

/-- A diagonal local descriptor selects its unique doubled reversed affine
word. -/
theorem diagonalScaledReversedDirectionWord_eq_of_matches
    (selectedShape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : selectedShape.Matches pair.1) :
    diagonalScaledReversedDirectionWord (descriptorPairTokens pair) =
      selectedShape.scaledReversedDirectionWord .first pair := by
  unfold diagonalScaledReversedDirectionWord
    guardedScaledReversedDirectionWords
  rw [flatMap_eq_selected_of_nodup allRouteShapes
    allRouteShapes_nodup
    (fun shape => shape.guardedScaledReversedDirectionWord
      (descriptorPairTokens pair))
    selectedShape (mem_allRouteShapes selectedShape)]
  · rw [selectedShape.guardedScaledReversedDirectionWord_descriptorPairTokens]
    simp [sameEdge, shapeMatches]
  · intro shape _ shapeNe
    have notMatches : ¬ shape.Matches pair.1 := by
      intro otherMatches
      exact shapeNe (RouteShape.eq_of_matches otherMatches shapeMatches)
    rw [shape.guardedScaledReversedDirectionWord_descriptorPairTokens]
    simp [sameEdge, notMatches]

/-- Off-diagonal pairs contribute nothing. -/
theorem diagonalScaledReversedDirectionWord_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    diagonalScaledReversedDirectionWord (descriptorPairTokens pair) = [] := by
  unfold diagonalScaledReversedDirectionWord
    guardedScaledReversedDirectionWords
  apply List.flatMap_eq_nil_iff.mpr
  intro shape _
  rw [shape.guardedScaledReversedDirectionWord_descriptorPairTokens]
  simp [edgeIndexNe]

/-- A numeric diagonal emits the doubled raw route traversed backward. -/
theorem diagonalScaledReversedDirectionWord_numeric_diagonal
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (descriptor : RouteDescriptor)
    (descriptorMember :
      descriptor ∈ PeriodicCNF.numericRouteDescriptors formula) :
    diagonalScaledReversedDirectionWord
        (descriptorPairTokens (descriptor, descriptor)) =
      Gadget.unitSubdivisionDirections
        (scalePolyline 2 descriptor.route).reverse := by
  rcases PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
      formula forward descriptor descriptorMember with
    ⟨shape, shapeMatches⟩
  rw [diagonalScaledReversedDirectionWord_eq_of_matches
    shape (descriptor, descriptor) rfl shapeMatches]
  apply shape.scaledReversedDirectionWord_eq
      .first (descriptor, descriptor)
  · simpa [descriptorAt] using shapeMatches
  · intro segment segmentMember
    exact PeriodicCNF.numericRouteDescriptor_segment_axisAligned
      formula wellFormed degree isLocal descriptorMember segmentMember

/-- Map the selector over all complete descriptor-pair blocks. -/
def diagonalScaledReversedDirectionStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List AxisDirection :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    diagonalScaledReversedDirectionWord tokens

noncomputable def
    diagonalScaledReversedDirectionStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      diagonalScaledReversedDirectionStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    diagonalScaledReversedDirectionWordComputableInPolyTime isPairEnd

@[simp] theorem
    diagonalScaledReversedDirectionStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    diagonalScaledReversedDirectionStream (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        diagonalScaledReversedDirectionWord (descriptorPairTokens pair) := by
  exact mappedOutput_encodeDescriptorPairs
    diagonalScaledReversedDirectionWord pairs

/-- The numeric descriptor square produces all doubled reversed raw route
words in original descriptor order. -/
theorem diagonalScaledReversedDirectionStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    diagonalScaledReversedDirectionStream
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        Gadget.unitSubdivisionDirections
          (scalePolyline 2 descriptor.route).reverse := by
  rw [diagonalScaledReversedDirectionStream_encodeDescriptorPairs]
  rw [PeriodicCNF.numericRouteDescriptorSquare_flatMap_diagonal_of_offDiagonal
    formula
    (fun pair => diagonalScaledReversedDirectionWord
      (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    exact diagonalScaledReversedDirectionWord_numeric_diagonal
      formula wellFormed degree isLocal forward descriptor descriptorMember
  · intro first _ second _ edgeIndexNe
    exact diagonalScaledReversedDirectionWord_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
