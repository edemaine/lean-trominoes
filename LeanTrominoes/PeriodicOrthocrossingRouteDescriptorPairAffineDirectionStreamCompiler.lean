/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
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

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
