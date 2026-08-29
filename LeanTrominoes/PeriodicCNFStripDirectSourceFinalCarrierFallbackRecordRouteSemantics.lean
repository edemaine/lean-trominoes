/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackRecordQuerySemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordBlockRouteSemantics

/-! # Direct carrier fallback record-route alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierRecordRouteStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierRecordRouteVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem directSourceFinalCarrierFallbackPrefixWords_eq_geometries
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

/-- The complete compiled carrier route words are exactly the four routes
stored in every declarative carrier fallback record block. -/
theorem directSourceFinalCarrierFallbackRouteDirections_eq_blockRoutes
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackRouteDirections decider symbols =
      BinaryRouteTailRecordProfileFraming.blockRoutes
        (directSourceFinalCarrierFallbackRecordBlocks decider symbols) := by
  rw [directSourceFinalCarrierFallbackRouteDirections_eq_geometric]
  unfold directSourceFinalCarrierFallbackGeometricDirections
  rw [directSourceFinalCarrierFallbackPrefixWords_eq_geometries,
    directSourceFinalCarrierFallbackSemanticQueries_eq_queryBlocks]
  unfold directSourceFinalCarrierFallbackRecordBlocks
  exact
    (CarrierFallbackRouteTailRecords.blockRoutes_blocks
      (directSourceFinalCarrierFallbackRecordGeometries decider symbols)
      (directSourceFinalCarrierOccurrenceSlots decider symbols)).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
