/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackRecordProfileCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackRouteTailRecordData

/-! # Alignment of compiled and declarative carrier record profiles -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierRecordProfileSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierRecordProfileSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem carrier_blockProfiles_blocks
    (geometries : List CarrierFallbackRouteTailRecords.Geometry)
    (slots : List RetainedTerminalSlot)
    (lengthEq : slots.length = 4 * geometries.length) :
    BinaryRouteTailRecordProfileFraming.blockProfiles
        (CarrierFallbackRouteTailRecords.blocks geometries slots) =
      geometries.flatMap fun geometry =>
        [BinaryRouteTailRecordFormatter.descriptorProfile
            (carrierClauseDescriptor
              geometry.horizontal geometry.nextSlice true),
          BinaryRouteTailRecordFormatter.descriptorProfile
            (carrierClauseDescriptor
              geometry.horizontal geometry.nextSlice false)] := by
  induction geometries generalizing slots with
  | nil =>
      have slotsNil : slots = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst slots
      rfl
  | cons geometry geometries induction =>
      rcases slots with _ | ⟨first, slots⟩
      · simp at lengthEq
      rcases slots with _ | ⟨second, slots⟩
      · simp at lengthEq
        omega
      rcases slots with _ | ⟨third, slots⟩
      · simp at lengthEq
        omega
      rcases slots with _ | ⟨fourth, slots⟩
      · simp at lengthEq
        omega
      have tailLength : slots.length = 4 * geometries.length := by
        simp only [List.length_cons] at lengthEq
        omega
      simp only [CarrierFallbackRouteTailRecords.blocks,
        BinaryRouteTailRecordProfileFraming.blockProfiles,
        List.flatMap_cons]
      dsimp only [CarrierFallbackRouteTailRecords.block]
      apply congrArg (fun tail =>
        [BinaryRouteTailRecordFormatter.descriptorProfile
            (carrierClauseDescriptor
              geometry.horizontal geometry.nextSlice true),
          BinaryRouteTailRecordFormatter.descriptorProfile
            (carrierClauseDescriptor
              geometry.horizontal geometry.nextSlice false)] ++ tail)
      change
        BinaryRouteTailRecordProfileFraming.blockProfiles
            (CarrierFallbackRouteTailRecords.blocks geometries slots) = _
      exact induction slots tailLength

private theorem recordProfiles_carrierLensRouteTailRecordBlock
    (geometry : CarrierFallbackRouteTailRecords.Geometry) :
    BinaryRouteTailRecordProfileFraming.recordProfiles
        (carrierLensRouteTailRecordBlock geometry.horizontal
          geometry.nextSlice geometry.span) =
      [BinaryRouteTailRecordFormatter.descriptorProfile
          (carrierClauseDescriptor
            geometry.horizontal geometry.nextSlice true),
        BinaryRouteTailRecordFormatter.descriptorProfile
          (carrierClauseDescriptor
            geometry.horizontal geometry.nextSlice false)] := by
  unfold carrierLensRouteTailRecordBlock
  rw [BinaryRouteTailRecordProfileFraming.recordProfiles_append]
  simp only [binaryRouteTailRecord, carrierClauseDescriptor]
  rw [BinaryRouteTailRecordProfileFraming.recordProfiles_clauseRecord,
    BinaryRouteTailRecordProfileFraming.recordProfiles_clauseRecord]
  rfl

private theorem directSourceCarrierRouteTailRecordTokens_eq_geometries
    (symbols : List encoding.Γ) :
    directSourceCarrierRouteTailRecordTokens decider symbols =
      (directSourceFinalCarrierFallbackRecordGeometries
        decider symbols).flatMap fun geometry =>
          carrierLensRouteTailRecordBlock geometry.horizontal
            geometry.nextSlice geometry.span := by
  rw [directSourceCarrierRouteTailRecordTokens_eq]
  unfold directSourceFinalCarrierFallbackRecordGeometries
    directSourceFinalCarrierFallbackEntries
    CarrierFallbackRouteTailRecords.selectedGeometries
  simp only [List.flatMap_assoc]
  apply List.flatMap_congr
  intro first _firstMember
  apply List.flatMap_congr
  intro second _secondMember
  by_cases retained :
      CarrierRankOrderedPairs.retainedPredicate first second
  · simp [retained]
  · simp [retained]

/-- The compiled carrier header stream is exactly the two profiles stored
in every declarative final fallback block. -/
theorem directSourceFinalCarrierFallbackCompiledRecordProfiles_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackCompiledRecordProfiles
        decider symbols =
      BinaryRouteTailRecordProfileFraming.blockProfiles
        (directSourceFinalCarrierFallbackRecordBlocks decider symbols) := by
  unfold directSourceFinalCarrierFallbackCompiledRecordProfiles
  rw [directSourceCarrierRouteTailRecordTokens_eq_geometries]
  rw [BinaryRouteTailRecordProfileFraming.recordProfiles_flatMap]
  unfold directSourceFinalCarrierFallbackRecordBlocks
  rw [carrier_blockProfiles_blocks _ _
    (directSourceFinalCarrierFallbackRecordSlots_length decider symbols)]
  apply List.flatMap_congr
  intro geometry _geometryMember
  exact recordProfiles_carrierLensRouteTailRecordBlock geometry

end LeanTrominoes.PeriodicCNFStripReduction

end
