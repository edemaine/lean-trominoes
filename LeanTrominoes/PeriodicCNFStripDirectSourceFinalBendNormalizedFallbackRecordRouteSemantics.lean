/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackRecordQuerySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackRouteDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackRouteTailRecordData
import LeanTrominoes.PeriodicOrthocrossingBendNormalizedFallbackRouteTailRecordBlockSemantics

/-! # Direct normalized bend fallback record-route alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendNormalizedRecordRouteStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendNormalizedRecordRouteVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem directSourceFinalBendNormalizedFallbackPrefixWords_eq_geometries
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackPrefixWords decider symbols =
      (directSourceFinalBendFallbackRecordGeometries
        decider symbols).flatMap
          BendFallbackRouteTailRecords.Geometry.prefixWords := by
  exact (directSourceFinalBendFallbackRecordGeometry_prefixWords
    decider symbols).symm

/-- The complete normalized bend compiler stream is exactly the four-route
projection of the direct normalized declarative blocks. -/
theorem directSourceFinalBendNormalizedFallbackRouteDirections_eq_blockRoutes
    (symbols : List encoding.Γ) :
    directSourceFinalBendNormalizedFallbackRouteDirections decider symbols =
      BinaryRouteTailRecordProfileFraming.blockRoutes
        (directSourceFinalBendNormalizedFallbackRecordBlocks
          decider symbols) := by
  rw [directSourceFinalBendNormalizedFallbackRouteDirections_eq_geometric]
  unfold directSourceFinalBendNormalizedFallbackGeometricDirections
  rw [directSourceFinalBendNormalizedFallbackPrefixWords_eq_geometries,
    directSourceFinalBendFallbackSemanticQueries_eq_queryBlocks]
  unfold directSourceFinalBendNormalizedFallbackRecordBlocks
  exact
    (BendNormalizedFallbackRouteTailRecords.blockRoutes_blocks
      (directSourceFinalBendFallbackRecordGeometries decider symbols)
      (directSourceFinalBendOccurrenceSlots decider symbols)).symm

/-- Normalization changes only route fields, so the direct bend block profile
stream agrees with the existing raw declarative blocks. -/
theorem directSourceFinalBendNormalizedFallbackRecordBlockProfiles_eq
    (symbols : List encoding.Γ) :
    BinaryRouteTailRecordProfileFraming.blockProfiles
        (directSourceFinalBendNormalizedFallbackRecordBlocks
          decider symbols) =
      BinaryRouteTailRecordProfileFraming.blockProfiles
        (directSourceFinalBendFallbackRecordBlocks decider symbols) := by
  unfold directSourceFinalBendNormalizedFallbackRecordBlocks
    directSourceFinalBendFallbackRecordBlocks
  exact BendNormalizedFallbackRouteTailRecords.blockProfiles_blocks _ _

/-- The fixed batch formatter serializes the named normalized bend blocks. -/
@[simp] theorem directSourceFinalBendNormalizedFallbackRecordFormatter_output
    (symbols : List encoding.Γ) :
    BinaryRouteTailRecordBatchFormatter.output
        (directSourceFinalBendNormalizedFallbackRecordInputTokens
          decider symbols) =
      directSourceFinalBendNormalizedFallbackRouteTailRecordTokens
        decider symbols := by
  unfold directSourceFinalBendNormalizedFallbackRecordInputTokens
    directSourceFinalBendNormalizedFallbackRouteTailRecordTokens
  exact BinaryRouteTailRecordBatchFormatter.output_tokens _

end LeanTrominoes.PeriodicCNFStripReduction

end
