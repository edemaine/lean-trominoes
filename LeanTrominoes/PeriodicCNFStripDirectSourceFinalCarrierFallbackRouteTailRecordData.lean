/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackRouteDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceSlotSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordBlockSemantics

/-! # Direct-source retained-carrier fallback record data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierFallbackRecordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierFallbackRecordDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

def directSourceFinalCarrierFallbackRecordGeometries
    (symbols : List encoding.Γ) :
    List CarrierFallbackRouteTailRecords.Geometry :=
  CarrierFallbackRouteTailRecords.selectedGeometries
    (directSourceFinalCarrierFallbackEntries decider symbols)

def directSourceFinalCarrierFallbackRecordBlocks
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Block :=
  CarrierFallbackRouteTailRecords.blocks
    (directSourceFinalCarrierFallbackRecordGeometries decider symbols)
    (directSourceFinalCarrierOccurrenceSlots decider symbols)

def directSourceFinalCarrierFallbackRecordInputTokens
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Token :=
  BinaryRouteTailRecordBatchFormatter.tokens
    (directSourceFinalCarrierFallbackRecordBlocks decider symbols)

def directSourceFinalCarrierFallbackRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  BinaryRouteTailRecordBatchFormatter.records
    (directSourceFinalCarrierFallbackRecordBlocks decider symbols)

/-- The direct record geometries project to the exact retained-carrier
prefix block stream already identified at the route-direction boundary. -/
@[simp] theorem directSourceFinalCarrierFallbackRecordGeometry_prefixBlocks
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierFallbackRecordGeometries
        decider symbols).map
          CarrierFallbackRouteTailRecords.Geometry.prefixBlock =
      directSourceFinalCarrierFallbackPrefixBlocks decider symbols := by
  unfold directSourceFinalCarrierFallbackRecordGeometries
    directSourceFinalCarrierFallbackPrefixBlocks
  exact CarrierFallbackRouteTailRecords.map_prefixBlock_selectedGeometries _

/-- There are exactly four selected final occurrence slots for each retained
carrier geometry. -/
theorem directSourceFinalCarrierFallbackRecordSlots_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierOccurrenceSlots decider symbols).length =
      4 * (directSourceFinalCarrierFallbackRecordGeometries
        decider symbols).length := by
  have aligned :=
    directSourceFinalCarrierFallbackRolesSlots_length decider symbols
  unfold directSourceFinalCarrierFallbackHeaderRoles at aligned
  rw [directSourceFinalCarrierFallbackTerminalDirections_eq,
    FallbackSuffixHeaderRoles.carrierRoles_length] at aligned
  simp only [List.length_map] at aligned
  have terminalLength :
      (directSourceFinalCarrierFallbackTerminalData
          decider symbols).length =
        4 * (directSourceFinalCarrierFallbackPrefixBlocks
          decider symbols).length := by
    unfold directSourceFinalCarrierFallbackTerminalData
      CarrierFallbackTerminalData.terminalData
      directSourceFinalCarrierFallbackPrefixBlocks
    simp [List.length_flatMap, Nat.mul_comm]
  have geometryLength := congrArg List.length
    (directSourceFinalCarrierFallbackRecordGeometry_prefixBlocks
      decider symbols)
  simp only [List.length_map] at geometryLength
  omega

/-- Consequently the direct carrier record-block zipper consumes every
selected geometry. -/
@[simp] theorem directSourceFinalCarrierFallbackRecordBlocks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierFallbackRecordBlocks decider symbols).length =
      (directSourceFinalCarrierFallbackRecordGeometries
        decider symbols).length := by
  unfold directSourceFinalCarrierFallbackRecordBlocks
  exact CarrierFallbackRouteTailRecords.blocks_length _ _
    (directSourceFinalCarrierFallbackRecordSlots_length decider symbols)

/-- Running the fixed batch formatter over the direct carrier input gives
the named direct carrier fallback record word. -/
@[simp] theorem directSourceFinalCarrierFallbackRecordFormatter_output
    (symbols : List encoding.Γ) :
    BinaryRouteTailRecordBatchFormatter.output
        (directSourceFinalCarrierFallbackRecordInputTokens
          decider symbols) =
      directSourceFinalCarrierFallbackRouteTailRecordTokens
        decider symbols := by
  unfold directSourceFinalCarrierFallbackRecordInputTokens
    directSourceFinalCarrierFallbackRouteTailRecordTokens
  exact BinaryRouteTailRecordBatchFormatter.output_tokens _

end LeanTrominoes.PeriodicCNFStripReduction

end
