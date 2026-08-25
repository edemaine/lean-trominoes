/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMap
import LeanTrominoes.PaddedSupportedCandidateValueMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldData
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData

/-! # Generic terminal-zero carrier field alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem Segment.map_terminalCarrierNodeTemplateBlock_of_terminal_zero
    (project : CarrierNode → Nat)
    (terminalZero : ∀ terminal, project (.terminal terminal) = 0)
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
        (Template.mapValue project) =
      (segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
        (Template.mapValue fun _ => 0) := by
  unfold Segment.terminalCarrierNodeTemplateBlock
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro translate _translateMember
  simp [Template.mapValue, terminalZero]

@[simp] theorem Segment.map_terminalCarrierNodeTemplateBlocks_of_terminal_zero
    (project : CarrierNode → Nat)
    (terminalZero : ∀ terminal, project (.terminal terminal) = 0)
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex).map
        (List.map (Template.mapValue project)) =
      (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex).map
        (List.map (Template.mapValue fun _ => 0)) := by
  simp [Segment.terminalCarrierNodeTemplateBlocks, terminalZero]

@[simp] theorem RouteShape.map_terminalCarrierNodeTemplateBlocks_of_terminal_zero
    (project : CarrierNode → Nat)
    (terminalZero : ∀ terminal, project (.terminal terminal) = 0)
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    (shape.terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue project)) =
      (shape.terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue fun _ => 0)) := by
  unfold RouteShape.terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro tagged _taggedMember
  exact tagged.1.map_terminalCarrierNodeTemplateBlocks_of_terminal_zero
    project terminalZero pair tagged.2

@[simp] theorem map_terminalCarrierNodeTemplateBlocks_of_terminal_zero
    (project : CarrierNode → Nat)
    (terminalZero : ∀ terminal, project (.terminal terminal) = 0)
    (pair : RouteDescriptor × RouteDescriptor) :
    (terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue project)) =
      (terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue fun _ => 0)) := by
  unfold terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro shape _shapeMember
  exact shape.map_terminalCarrierNodeTemplateBlocks_of_terminal_zero
    project terminalZero pair

@[simp] theorem map_paddedTerminalCarrierNodeCandidates_of_terminal_zero
    (project : CarrierNode → Nat)
    (terminalZero : ∀ terminal, project (.terminal terminal) = 0)
    (pair : RouteDescriptor × RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidates pair).map
        (Candidate.mapValue project) =
      (paddedTerminalCarrierNodeCandidates pair).map
        (Candidate.mapValue fun _ => 0) := by
  unfold paddedTerminalCarrierNodeCandidates
  rw [candidates_mapValue, candidates_mapValue]
  rw [map_terminalCarrierNodeTemplateBlocks_of_terminal_zero
    project terminalZero]

@[simp] theorem map_paddedTerminalCarrierNodeCandidateStream_of_terminal_zero
    (project : CarrierNode → Nat)
    (terminalZero : ∀ terminal, project (.terminal terminal) = 0)
    (descriptors : List RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue project) =
      (paddedTerminalCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue fun _ => 0) := by
  unfold paddedTerminalCarrierNodeCandidateStream
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  exact map_paddedTerminalCarrierNodeCandidates_of_terminal_zero
    project terminalZero pair

def optionalProjectedValue (project : CarrierNode → Nat) :
    Option CarrierNode → Nat
  | none => 0
  | some node => project node

private theorem candidates_forall₂_optionalProjectedValue
    (project : CarrierNode → Nat)
    (candidates : List (Candidate CarrierNode)) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = project node)
      candidates
      ((PaddedSupportedLastRepresentativeEqualityRows.values candidates).map
        (optionalProjectedValue project)) := by
  unfold PaddedSupportedLastRepresentativeEqualityRows.values
  induction candidates with
  | nil => exact List.Forall₂.nil
  | cons candidate candidates induction =>
      simp only [List.map_cons]
      exact List.Forall₂.cons
        (by
          intro node valueEq
          rw [valueEq]
          rfl)
        induction

/-- The reusable physical terminal-zero stream is aligned with every padded
terminal candidate for any field that vanishes on terminal nodes. -/
theorem terminalZeroFields_forall₂
    (project : CarrierNode → Nat)
    (terminalZero : ∀ terminal, project (.terminal terminal) = 0)
    (descriptors : List RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = project node)
      (paddedTerminalCarrierNodeCandidateStream descriptors)
      ((CarrierBoundaryPresenceField.terminalKeys descriptors).map
        (GuardedPresenceFieldProjector.value false)) := by
  have valuesEq :
      (CarrierBoundaryPresenceField.terminalKeys descriptors).map
          (GuardedPresenceFieldProjector.value false) =
        (PaddedSupportedLastRepresentativeEqualityRows.values
          (paddedTerminalCarrierNodeCandidateStream descriptors)).map
            (optionalProjectedValue project) := by
    calc
      _ = (PaddedSupportedLastRepresentativeEqualityRows.values
            ((paddedTerminalCarrierNodeCandidateStream descriptors).map
              (Candidate.mapValue fun _ : CarrierNode => 0))).map
            fun value => value.getD 0 := by
          unfold CarrierBoundaryPresenceField.terminalKeys
          rw [values_map_mapValue]
          simp only [List.map_map]
          apply List.map_congr_left
          intro value _valueMember
          cases value <;> rfl
      _ = (PaddedSupportedLastRepresentativeEqualityRows.values
            ((paddedTerminalCarrierNodeCandidateStream descriptors).map
              (Candidate.mapValue project))).map
            fun value => value.getD 0 := by
          exact congrArg
            (fun candidates =>
              (PaddedSupportedLastRepresentativeEqualityRows.values
                candidates).map fun value => value.getD 0)
            (map_paddedTerminalCarrierNodeCandidateStream_of_terminal_zero
              project terminalZero descriptors).symm
      _ = _ := by
        rw [values_map_mapValue]
        rw [List.map_map]
        apply List.map_congr_left
        intro value _valueMember
        cases value <;> rfl
  rw [valuesEq]
  exact candidates_forall₂_optionalProjectedValue project _

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
