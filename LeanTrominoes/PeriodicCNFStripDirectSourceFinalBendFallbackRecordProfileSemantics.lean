/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackRecordProfileCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackRouteTailRecordData

/-! # Alignment of compiled and declarative bend record profiles -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendRecordProfileSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendRecordProfileSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem bend_blockProfiles_blocks
    (geometries : List BendFallbackRouteTailRecords.Geometry)
    (slots : List RetainedTerminalSlot)
    (lengthEq : slots.length = 4 * geometries.length) :
    BinaryRouteTailRecordProfileFraming.blockProfiles
        (BendFallbackRouteTailRecords.blocks geometries slots) =
      geometries.flatMap fun geometry =>
        [BinaryRouteTailRecordFormatter.descriptorProfile
            (bendClauseDescriptor
              geometry.firstPort geometry.secondPort false true),
          BinaryRouteTailRecordFormatter.descriptorProfile
            (bendClauseDescriptor
              geometry.firstPort geometry.secondPort false false)] := by
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
      simp only [BendFallbackRouteTailRecords.blocks,
        BinaryRouteTailRecordProfileFraming.blockProfiles,
        List.flatMap_cons]
      dsimp only [BendFallbackRouteTailRecords.block]
      apply congrArg (fun tail =>
        [BinaryRouteTailRecordFormatter.descriptorProfile
            (bendClauseDescriptor
              geometry.firstPort geometry.secondPort false true),
          BinaryRouteTailRecordFormatter.descriptorProfile
            (bendClauseDescriptor
              geometry.firstPort geometry.secondPort false false)] ++ tail)
      change
        BinaryRouteTailRecordProfileFraming.blockProfiles
            (BendFallbackRouteTailRecords.blocks geometries slots) = _
      exact induction slots tailLength

private theorem recordProfiles_bendRouteTailRecordBlock
    (geometry : BendFallbackRouteTailRecords.Geometry) :
    BinaryRouteTailRecordProfileFraming.recordProfiles
        (bendRouteTailRecordBlock geometry.firstPort geometry.secondPort
          false) =
      [BinaryRouteTailRecordFormatter.descriptorProfile
          (bendClauseDescriptor
            geometry.firstPort geometry.secondPort false true),
        BinaryRouteTailRecordFormatter.descriptorProfile
          (bendClauseDescriptor
            geometry.firstPort geometry.secondPort false false)] := by
  unfold bendRouteTailRecordBlock
  rw [BinaryRouteTailRecordProfileFraming.recordProfiles_append]
  simp only [binaryRouteTailRecord, bendClauseDescriptor]
  rw [BinaryRouteTailRecordProfileFraming.recordProfiles_clauseRecord,
    BinaryRouteTailRecordProfileFraming.recordProfiles_clauseRecord]
  rfl

private theorem directSourceBaseBendRouteTailRecordTokens_eq_geometries
    (symbols : List encoding.Γ) :
    directSourceBaseBendRouteTailRecordTokens decider symbols =
      (directSourceFinalBendFallbackRecordGeometries
        decider symbols).flatMap fun geometry =>
          bendRouteTailRecordBlock geometry.firstPort
            geometry.secondPort false := by
  rw [directSourceBaseBendRouteTailRecordTokens_eq]
  unfold directSourceFinalBendFallbackRecordGeometries
    BendFallbackRouteTailRecords.selectedGeometries
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro descriptor _descriptorMember
  rw [List.flatMap_map]

/-- The compiled bend header stream is exactly the two profiles stored in
every declarative final fallback block. -/
theorem directSourceFinalBendFallbackCompiledRecordProfiles_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackCompiledRecordProfiles decider symbols =
      BinaryRouteTailRecordProfileFraming.blockProfiles
        (directSourceFinalBendFallbackRecordBlocks decider symbols) := by
  unfold directSourceFinalBendFallbackCompiledRecordProfiles
  rw [directSourceBaseBendRouteTailRecordTokens_eq_geometries]
  rw [BinaryRouteTailRecordProfileFraming.recordProfiles_flatMap]
  unfold directSourceFinalBendFallbackRecordBlocks
  rw [bend_blockProfiles_blocks _ _
    (directSourceFinalBendFallbackRecordSlots_length decider symbols)]
  apply List.flatMap_congr
  intro geometry _geometryMember
  exact recordProfiles_bendRouteTailRecordBlock geometry

end LeanTrominoes.PeriodicCNFStripReduction

end
