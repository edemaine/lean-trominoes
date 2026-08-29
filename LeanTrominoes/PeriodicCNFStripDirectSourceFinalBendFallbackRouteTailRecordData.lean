/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackRouteDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceSlotSemantics
import LeanTrominoes.PeriodicOrthocrossingBendFallbackRouteTailRecordBlockSemantics

/-! # Direct-source retained-bend fallback record data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendFallbackRecordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendFallbackRecordDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

def directSourceFinalBendFallbackRecordGeometries
    (symbols : List encoding.Γ) :
    List BendFallbackRouteTailRecords.Geometry :=
  BendFallbackRouteTailRecords.selectedGeometries
    (PeriodicCNF.numericRouteDescriptors
      (directSourceFormula decider symbols))

def directSourceFinalBendFallbackRecordBlocks
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Block :=
  BendFallbackRouteTailRecords.blocks
    (directSourceFinalBendFallbackRecordGeometries decider symbols)
    (directSourceFinalBendOccurrenceSlots decider symbols)

def directSourceFinalBendFallbackRecordInputTokens
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Token :=
  BinaryRouteTailRecordBatchFormatter.tokens
    (directSourceFinalBendFallbackRecordBlocks decider symbols)

def directSourceFinalBendFallbackRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  BinaryRouteTailRecordBatchFormatter.records
    (directSourceFinalBendFallbackRecordBlocks decider symbols)

/-- Flattening the direct bend geometries recovers the exact established
scaled-prefix word stream. -/
theorem directSourceFinalBendFallbackRecordGeometry_prefixWords
    (symbols : List encoding.Γ) :
    (directSourceFinalBendFallbackRecordGeometries
      decider symbols).flatMap
        BendFallbackRouteTailRecords.Geometry.prefixWords =
      directSourceFinalBendFallbackPrefixWords decider symbols := by
  unfold directSourceFinalBendFallbackRecordGeometries
    BendFallbackRouteTailRecords.selectedGeometries
    directSourceFinalBendFallbackPrefixWords
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro descriptor _descriptorMember
  rw [List.flatMap_map]
  rfl

theorem directSourceFinalBendFallbackRecordSlots_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendOccurrenceSlots decider symbols).length =
      4 * (directSourceFinalBendFallbackRecordGeometries
        decider symbols).length := by
  have aligned :=
    directSourceFinalBendFallbackRolesSlots_length decider symbols
  unfold directSourceFinalBendFallbackHeaderRoles at aligned
  rw [directSourceFinalBendFallbackTerminalDirections_eq,
    FallbackSuffixHeaderRoles.bendRoles_length] at aligned
  simp only [List.length_map] at aligned
  have terminalLength :
      (directSourceFinalBendFallbackTerminalData decider symbols).length =
        4 * (directSourceFinalBendFallbackRecordGeometries
          decider symbols).length := by
    let descriptors := PeriodicCNF.numericRouteDescriptors
      (directSourceFormula decider symbols)
    change
      (descriptors.flatMap fun descriptor =>
        (routeBends descriptor.edgeIndex (0, 0)
          descriptor.route).flatMap fun routeBend =>
            PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.bendRouteTerminalDataBlock
              routeBend.incomingPort routeBend.outgoingPort).length =
        4 * (BendFallbackRouteTailRecords.selectedGeometries
          descriptors).length
    unfold BendFallbackRouteTailRecords.selectedGeometries
    induction descriptors with
    | nil => rfl
    | cons descriptor descriptors induction =>
        simp only [List.flatMap_cons, List.length_append,
          List.length_map]
        have headLength :
            ((routeBends descriptor.edgeIndex (0, 0)
              descriptor.route).flatMap fun routeBend =>
                PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.bendRouteTerminalDataBlock
                  routeBend.incomingPort routeBend.outgoingPort).length =
              4 * (routeBends descriptor.edgeIndex (0, 0)
                descriptor.route).length := by
          simp [List.length_flatMap, Nat.mul_comm]
        rw [headLength, induction]
        omega
  omega

@[simp] theorem directSourceFinalBendFallbackRecordBlocks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendFallbackRecordBlocks decider symbols).length =
      (directSourceFinalBendFallbackRecordGeometries
        decider symbols).length := by
  unfold directSourceFinalBendFallbackRecordBlocks
  exact BendFallbackRouteTailRecords.blocks_length _ _
    (directSourceFinalBendFallbackRecordSlots_length decider symbols)

@[simp] theorem directSourceFinalBendFallbackRecordFormatter_output
    (symbols : List encoding.Γ) :
    BinaryRouteTailRecordBatchFormatter.output
        (directSourceFinalBendFallbackRecordInputTokens decider symbols) =
      directSourceFinalBendFallbackRouteTailRecordTokens decider symbols := by
  unfold directSourceFinalBendFallbackRecordInputTokens
    directSourceFinalBendFallbackRouteTailRecordTokens
  exact BinaryRouteTailRecordBatchFormatter.output_tokens _

end LeanTrominoes.PeriodicCNFStripReduction

end
