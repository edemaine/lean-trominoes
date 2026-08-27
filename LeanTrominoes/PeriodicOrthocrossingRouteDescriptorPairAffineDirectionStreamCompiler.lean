/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSegmentGeometry
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSquareDiagonal
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineGuardedDirectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelectionSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Selecting affine direction words over descriptor-pair streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags

/-- Concatenate the dynamic candidate words of a fixed list of shapes. -/
def guardedDirectionWords
    (shapes : List RouteShape)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List AxisDirection :=
  shapes.flatMap fun shape => shape.guardedDirectionWord tokens

/-- Select the unique diagonal route direction word among all 28 shapes. -/
def diagonalDirectionWord
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List AxisDirection :=
  guardedDirectionWords allRouteShapes tokens

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- A fixed list of guarded dynamic shape words can be concatenated in
polynomial time. -/
noncomputable def guardedDirectionWordsComputableInPolyTime :
    (shapes : List RouteShape) →
      TM2ComputableInPolyTime id id (guardedDirectionWords shapes)
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
      let first := shape.guardedDirectionWordComputableInPolyTime
      let rest := guardedDirectionWordsComputableInPolyTime shapes
      change TM2ComputableInPolyTime id id
        (fun tokens => shape.guardedDirectionWord tokens ++
          guardedDirectionWords shapes tokens)
      exact TM2ListAppend.computableInPolyTime first rest

/-- The complete 28-shape diagonal selector is polynomial-time computable. -/
noncomputable def diagonalDirectionWordComputableInPolyTime :
    TM2ComputableInPolyTime id id diagonalDirectionWord := by
  change TM2ComputableInPolyTime id id
    (guardedDirectionWords allRouteShapes)
  exact guardedDirectionWordsComputableInPolyTime allRouteShapes

private theorem flatMap_eq_of_unique
    {Index Output : Type}
    (indices : List Index) (function : Index → List Output)
    (selected : Index)
    (nodup : indices.Nodup)
    (selectedMember : selected ∈ indices)
    (othersEmpty :
      ∀ index ∈ indices, index ≠ selected → function index = []) :
    indices.flatMap function = function selected := by
  induction indices with
  | nil => simp at selectedMember
  | cons index indices induction =>
      rw [List.nodup_cons] at nodup
      rcases List.mem_cons.mp selectedMember with selectedHead | selectedTail
      · subst index
        rw [List.flatMap_cons]
        have tailEmpty : indices.flatMap function = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro other otherMember
          exact othersEmpty other (by simp [otherMember]) fun otherEq =>
            nodup.1 (otherEq ▸ otherMember)
        rw [tailEmpty, List.append_nil]
      · have headNe : index ≠ selected := by
          intro headEq
          exact nodup.1 (headEq ▸ selectedTail)
        rw [List.flatMap_cons,
          othersEmpty index (by simp) headNe,
          List.nil_append]
        exact induction nodup.2 selectedTail fun other otherMember otherNe =>
          othersEmpty other (by simp [otherMember]) otherNe

/-- On a diagonal canonical pair with a local shape, the complete selector
returns exactly that shape's affine direction word. -/
theorem diagonalDirectionWord_eq_of_matches
    (selectedShape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : selectedShape.Matches pair.1) :
    diagonalDirectionWord (descriptorPairTokens pair) =
      selectedShape.directionWord .first pair := by
  unfold diagonalDirectionWord guardedDirectionWords
  rw [flatMap_eq_of_unique allRouteShapes
    (fun shape =>
      shape.guardedDirectionWord (descriptorPairTokens pair))
    selectedShape allRouteShapes_nodup
    (mem_allRouteShapes selectedShape)]
  · rw [selectedShape.guardedDirectionWord_descriptorPairTokens]
    simp [sameEdge, shapeMatches]
  · intro shape _shapeMember shapeNe
    have notMatches : ¬shape.Matches pair.1 := by
      intro otherMatches
      exact shapeNe (RouteShape.eq_of_matches otherMatches shapeMatches)
    change shape.guardedDirectionWord (descriptorPairTokens pair) = []
    rw [shape.guardedDirectionWord_descriptorPairTokens]
    simp [sameEdge, notMatches]

/-- Every off-diagonal canonical pair is suppressed before its dynamic
direction word can contribute. -/
theorem diagonalDirectionWord_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    diagonalDirectionWord (descriptorPairTokens pair) = [] := by
  unfold diagonalDirectionWord guardedDirectionWords
  apply List.flatMap_eq_nil_iff.mpr
  intro shape _shapeMember
  rw [shape.guardedDirectionWord_descriptorPairTokens]
  simp [edgeIndexNe]

/-- A listed numeric descriptor's diagonal block is exactly its complete
unit-subdivision direction word. -/
theorem diagonalDirectionWord_numeric_diagonal
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (descriptor : RouteDescriptor)
    (descriptorMember :
      descriptor ∈ PeriodicCNF.numericRouteDescriptors formula) :
    diagonalDirectionWord
        (descriptorPairTokens (descriptor, descriptor)) =
      Gadget.unitSubdivisionDirections descriptor.route := by
  rcases PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
      formula forward descriptor descriptorMember with
    ⟨shape, shapeMatches⟩
  rw [diagonalDirectionWord_eq_of_matches
    shape (descriptor, descriptor) rfl shapeMatches]
  apply shape.directionWord_eq .first (descriptor, descriptor)
  · simpa [descriptorAt] using shapeMatches
  · intro segment segmentMember
    exact PeriodicCNF.numericRouteDescriptor_segment_axisAligned
      formula wellFormed degree isLocal descriptorMember segmentMember

/-- Map the complete diagonal selector independently over all delimited pair
blocks. -/
def diagonalDirectionStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List AxisDirection :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    diagonalDirectionWord tokens

noncomputable def diagonalDirectionStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id diagonalDirectionStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    diagonalDirectionWordComputableInPolyTime isPairEnd

@[simp] theorem diagonalDirectionStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    diagonalDirectionStream (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        diagonalDirectionWord (descriptorPairTokens pair) := by
  exact mappedOutput_encodeDescriptorPairs diagonalDirectionWord pairs

/-- On a numeric descriptor square, the stream selector removes every
off-diagonal pair and emits complete raw route directions in descriptor
order. -/
theorem diagonalDirectionStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    diagonalDirectionStream
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        Gadget.unitSubdivisionDirections descriptor.route := by
  rw [diagonalDirectionStream_encodeDescriptorPairs]
  rw [PeriodicCNF.numericRouteDescriptorSquare_flatMap_diagonal_of_offDiagonal
    formula
    (fun pair => diagonalDirectionWord (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    exact diagonalDirectionWord_numeric_diagonal
      formula wellFormed degree isLocal forward descriptor descriptorMember
  · intro first _firstMember second _secondMember edgeIndexNe
    exact diagonalDirectionWord_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
