/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendPredicateSemantics

/-! # Route-shape semantics of the affine retained-bend scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Block selection distributes across an aligned prefix append. -/
theorem selectTruthBlocks_append
    {Output : Type}
    (firstBlocks secondBlocks : List (List Output))
    (firstTruths secondTruths : List Bool)
    (lengthEq : firstBlocks.length = firstTruths.length) :
    selectTruthBlocks
        (firstBlocks ++ secondBlocks) (firstTruths ++ secondTruths) =
      selectTruthBlocks firstBlocks firstTruths ++
        selectTruthBlocks secondBlocks secondTruths := by
  induction firstBlocks generalizing firstTruths with
  | nil =>
      have firstTruthsNil : firstTruths = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using lengthEq.symm)
      subst firstTruths
      rfl
  | cons block blocks induction =>
      cases firstTruths with
      | nil => simp at lengthEq
      | cons truth truths =>
          have tailLengthEq : blocks.length = truths.length := by
            simpa using lengthEq
          simp only [List.cons_append, selectTruthBlocks]
          rw [induction truths tailLengthEq]
          cases truth <;> simp [List.append_assoc]

/-- Block selection distributes over a fixed aligned flat-map family. -/
theorem selectTruthBlocks_flatMap
    {Index Output : Type}
    (indices : List Index)
    (blocks : Index → List (List Output))
    (truths : Index → List Bool)
    (lengthEq :
      ∀ index ∈ indices, (blocks index).length = (truths index).length) :
    selectTruthBlocks
        (indices.flatMap blocks) (indices.flatMap truths) =
      indices.flatMap fun index =>
        selectTruthBlocks (blocks index) (truths index) := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.flatMap_cons]
      rw [selectTruthBlocks_append]
      · rw [induction]
        intro tailIndex tailMember
        exact lengthEq tailIndex (List.mem_cons_of_mem index tailMember)
      · exact lengthEq index (List.mem_cons_self)

/-- Under its guard and genuine-segment hypotheses, one route-shape scan is
exactly the canonical descriptor expansion of its evaluated base bends. -/
theorem RouteShape.bendDescriptorSelection_eq
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (incomingGenuine :
      ∀ template ∈ shape.baseBendTemplates,
        (AxisDirection.between
          (template.incomingStart.evalPair pair)
          (template.bend.evalPair pair)).IsGenuine)
    (outgoingGenuine :
      ∀ template ∈ shape.baseBendTemplates,
        (AxisDirection.between
          (template.bend.evalPair pair)
          (template.outgoingFinish.evalPair pair)).IsGenuine) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        shape.bendDescriptorBlocks
        (descriptorPairTokens pair) =
      shape.baseBendTemplates.flatMap fun template =>
        canonicalBendDescriptorBlock
          (template.evalPair .first pair).incomingPort
          (template.evalPair .first pair).outgoingPort false := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendDescriptorBlocks
  rw [List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_congr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.descriptorPredicates_selectedBlock
      shape pair sameEdge shapeMatches
      (incomingGenuine template templateMember)
      (outgoingGenuine template templateMember)
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates,
      bendTemplateDescriptorBlocks]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
