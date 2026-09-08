/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPositionTerminalStreamAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateNodeStreamSemantics
import LeanTrominoes.UnaryFieldBooleanFilterCompiler

/-! # Compiling physical terminal coordinates without inactive candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open Computability Turing PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

/-- Every segment contributes two ends in each of nine neighboring periods. -/
def terminalCoordinateActives (tokens : List Token) : List Bool :=
  (predicateListTruthValues terminalDirectionalPredicates tokens).flatMap
    (List.replicate 18)

noncomputable def terminalCoordinateActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id terminalCoordinateActives := by
  change TM2ComputableInPolyTime id id
    (fun tokens => (predicateListTruthValues terminalDirectionalPredicates tokens).flatMap
      (List.replicate 18))
  exact TM2CompositionMachine.computableInPolyTime
    (predicateListTruthValuesComputableInPolyTime terminalDirectionalPredicates)
    (FiniteBlockTransducer.computableInPolyTime (List.replicate 18))

def activeTerminalCoordinateFields (horizontal keepPositive : Bool)
    (tokens : List Token) : List Nat :=
  UnaryFieldBooleanFilter.selectedValues (terminalCoordinateActives tokens)
    (terminalCoordinateFields horizontal keepPositive tokens)

noncomputable def activeTerminalCoordinateFieldsComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (activeTerminalCoordinateFields horizontal keepPositive) := by
  exact UnaryFieldBooleanFilter.selectedValuesComputableInPolyTime id
    terminalCoordinateActives (terminalCoordinateFields horizontal keepPositive)
    terminalCoordinateActivesComputableInPolyTime
    (terminalCoordinateFieldsComputableInPolyTime horizontal keepPositive)

private theorem terminalTemplateBlock_length
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor) (index : Nat) :
    (segment.terminalCarrierNodeTemplateBlock pair index).length = 18 := by
  simp [Segment.terminalCarrierNodeTemplateBlock, neighborTranslations,
    neighborCoordinates]

private theorem terminalTemplateBlockLengths
    (pair : RouteDescriptor × RouteDescriptor) :
    (terminalDirectionalCarrierNodeTemplateBlocks pair).map List.length =
      List.replicate terminalDirectionalPredicates.length 18 := by
  simp [terminalDirectionalCarrierNodeTemplateBlocks, terminalDirectionalPredicates,
    RouteShape.terminalDirectionalCarrierNodeTemplateBlocks,
    RouteShape.terminalDirectionalPredicates,
    Segment.terminalDirectionalCarrierNodeTemplateBlocks,
    Segment.terminalDirectionalPredicates, terminalTemplateBlock_length,
    List.map_flatMap, List.length_flatMap]
  have blockRepeats {Item : Type} (items : List Item) :
      items.flatMap (fun _ => [18, 18, 18, 18]) =
        List.replicate (items.length * 4) 18 := by
    induction items with
    | nil => rfl
    | cons item items induction =>
        simp only [List.flatMap_cons, List.length_cons, induction]
        change List.replicate 4 18 ++ List.replicate (items.length * 4) 18 = _
        rw [← List.replicate_add]
        congr 1; omega
  simp_rw [blockRepeats, List.length_zipIdx]
  induction allRouteShapes with
  | nil => rfl
  | cons shape shapes induction =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons, induction]
      exact (List.replicate_add _ _ _).symm

private theorem activity_candidates
    {Value : Type} (actives : List Bool) (blocks : List (List (Template Value)))
    (sizes : blocks.map List.length = List.replicate actives.length 18) :
    (candidates actives blocks).map (fun candidate => candidate.value.isSome) =
      actives.flatMap (List.replicate 18) := by
  induction actives generalizing blocks with
  | nil => simp [candidates]
  | cons active actives induction =>
      cases blocks with
      | nil => simp at sizes
      | cons block blocks =>
          have headSize : block.length = 18 := by simpa using (List.cons.inj sizes).1
          have tailSizes : blocks.map List.length = List.replicate actives.length 18 := by
            simpa using (List.cons.inj sizes).2
          cases active <;> simp [candidates, List.map_append, List.map_map, Function.comp_def,
            Template.activate, headSize, induction blocks tailSizes]

/-- The finite activity pass marks exactly the populated terminal slots. -/
theorem terminalCoordinateActives_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor) :
    terminalCoordinateActives (descriptorPairTokens pair) =
      (terminalDirectionalCarrierNodeCandidates pair).map
        (fun candidate => candidate.value.isSome) := by
  unfold terminalCoordinateActives terminalDirectionalCarrierNodeCandidates
  rw [predicateListTruthValues_eq]
  symm
  apply activity_candidates
  simpa using terminalTemplateBlockLengths pair

private theorem select_aligned_candidates
    {Value : Type} (items : List (Candidate Value)) (values : List Nat)
    (field : Value → Nat)
    (aligned : List.Forall₂ (fun candidate value => ∀ item,
      candidate.value = some item → value = field item) items values) :
    UnaryFieldBooleanFilter.selectedValues
        (items.map fun candidate => candidate.value.isSome) values =
      (items.filterMap Candidate.value).map field := by
  rw [UnaryFieldBooleanFilter.selectedValues_eq]
  induction aligned with
  | nil => rfl
  | @cons candidate value candidates values head aligned induction =>
      cases valueEq : candidate.value with
      | none =>
          simpa [DelimitedBinaryWordBooleanFilter.selected, valueEq] using induction
      | some item =>
          have fieldEq := head item valueEq
          simp [DelimitedBinaryWordBooleanFilter.selected, valueEq, fieldEq, induction]

/-- Filtering the compiled fields emits exactly the physical coordinates of
active terminals, preserving their original order and multiplicity. -/
theorem activeTerminalCoordinateFields_descriptorPairTokens
    (horizontal keepPositive : Bool) (pair : RouteDescriptor × RouteDescriptor) :
    activeTerminalCoordinateFields horizontal keepPositive (descriptorPairTokens pair) =
      ((paddedTerminalCarrierNodeCandidates pair).filterMap Candidate.value).map
        (carrierNodeCoordinateFieldAtPeriod horizontal keepPositive pair.1.gridSize) := by
  unfold activeTerminalCoordinateFields
  rw [terminalCoordinateActives_descriptorPairTokens]
  rw [select_aligned_candidates _ _ _
    (terminalCoordinateCarrierNodeCandidates_forall₂ horizontal keepPositive pair)]
  rw [filterMap_terminalDirectionalCarrierNodeCandidates]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

end
