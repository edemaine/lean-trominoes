/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackRecordQuerySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedFallbackRouteDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedFallbackRouteTailRecordData
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedFallbackRouteTailRecordBlockSemantics

/-! # Direct normalized carrier fallback record-route alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierNormalizedRecordRouteStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierNormalizedRecordRouteVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem directSourceFinalCarrierNormalizedFallbackPrefixWords_eq_geometries
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackPrefixWords decider symbols =
      (directSourceFinalCarrierFallbackRecordGeometries
        decider symbols).flatMap fun geometry =>
          CarrierFallbackPrefixScaling.canonicalScaledPrefixWords
            geometry.horizontal geometry.span := by
  unfold directSourceFinalCarrierFallbackPrefixWords
  have prefixEq :=
    directSourceFinalCarrierFallbackRecordGeometry_prefixBlocks
      decider symbols
  rw [← prefixEq]
  rw [List.flatMap_map]
  rfl

/-- The complete normalized carrier compiler stream is exactly the four-route
projection of the direct normalized declarative blocks. -/
theorem directSourceFinalCarrierNormalizedFallbackRouteDirections_eq_blockRoutes
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierNormalizedFallbackRouteDirections
        decider symbols =
      BinaryRouteTailRecordProfileFraming.blockRoutes
        (directSourceFinalCarrierNormalizedFallbackRecordBlocks
          decider symbols) := by
  rw [directSourceFinalCarrierNormalizedFallbackRouteDirections_eq_geometric]
  unfold directSourceFinalCarrierNormalizedFallbackGeometricDirections
  rw [directSourceFinalCarrierNormalizedFallbackPrefixWords_eq_geometries,
    directSourceFinalCarrierFallbackSemanticQueries_eq_queryBlocks]
  unfold directSourceFinalCarrierNormalizedFallbackRecordBlocks
  exact
    (CarrierNormalizedFallbackRouteTailRecords.blockRoutes_blocks
      (directSourceFinalCarrierFallbackRecordGeometries decider symbols)
      (directSourceFinalCarrierOccurrenceSlots decider symbols)).symm

/-- Normalization changes only route fields, so the direct carrier block
profile stream agrees with the existing raw declarative blocks. -/
theorem directSourceFinalCarrierNormalizedFallbackRecordBlockProfiles_eq
    (symbols : List encoding.Γ) :
    BinaryRouteTailRecordProfileFraming.blockProfiles
        (directSourceFinalCarrierNormalizedFallbackRecordBlocks
          decider symbols) =
      BinaryRouteTailRecordProfileFraming.blockProfiles
        (directSourceFinalCarrierFallbackRecordBlocks decider symbols) := by
  unfold directSourceFinalCarrierNormalizedFallbackRecordBlocks
    directSourceFinalCarrierFallbackRecordBlocks
  exact CarrierNormalizedFallbackRouteTailRecords.blockProfiles_blocks _ _

/-- The fixed batch formatter serializes the named normalized carrier blocks. -/
@[simp] theorem directSourceFinalCarrierNormalizedFallbackRecordFormatter_output
    (symbols : List encoding.Γ) :
    BinaryRouteTailRecordBatchFormatter.output
        (directSourceFinalCarrierNormalizedFallbackRecordInputTokens
          decider symbols) =
      directSourceFinalCarrierNormalizedFallbackRouteTailRecordTokens
        decider symbols := by
  unfold directSourceFinalCarrierNormalizedFallbackRecordInputTokens
    directSourceFinalCarrierNormalizedFallbackRouteTailRecordTokens
  exact BinaryRouteTailRecordBatchFormatter.output_tokens _

end LeanTrominoes.PeriodicCNFStripReduction

end
