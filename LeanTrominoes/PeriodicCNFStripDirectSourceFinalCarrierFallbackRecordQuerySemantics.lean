/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackRouteTailRecordData
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryColumnSemantics

/-! # Direct carrier fallback record-query alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierRecordQueryStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierRecordQueryVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem carrier_alignedQueries_terminalBlocks
    (geometries : List CarrierFallbackRouteTailRecords.Geometry)
    (slots : List RetainedTerminalSlot)
    (lengthEq : slots.length = 4 * geometries.length) :
    let terminals := geometries.flatMap fun geometry =>
      carrierLensRouteTerminalDataBlock geometry.horizontal geometry.span
    FallbackSuffixQueryColumns.alignedQueries
        (FallbackSuffixHeaderRoles.carrierRoles
          (terminals.map Prod.fst))
        (terminals.map Prod.snd) slots =
      CarrierFallbackRouteTailRecords.queryBlocks geometries slots := by
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
      simp only [List.flatMap_cons, List.map_append,
        carrierLensRouteTerminalDataBlock, List.map_cons, List.map_nil,
        List.cons_append]
      rw [FallbackSuffixHeaderRoles.carrierRoles_four]
      change
        CarrierFallbackRouteTailRecords.queryBlock geometry
              first second third fourth ++
            FallbackSuffixQueryColumns.alignedQueries
              (FallbackSuffixHeaderRoles.carrierRoles
                ((geometries.flatMap fun geometry =>
                  carrierLensRouteTerminalDataBlock geometry.horizontal
                    geometry.span).map Prod.fst))
              ((geometries.flatMap fun geometry =>
                carrierLensRouteTerminalDataBlock geometry.horizontal
                  geometry.span).map Prod.snd)
              slots =
          CarrierFallbackRouteTailRecords.queryBlock geometry
              first second third fourth ++
            CarrierFallbackRouteTailRecords.queryBlocks geometries slots
      rw [induction slots tailLength]

private theorem directSourceFinalCarrierFallbackTerminalData_eq_geometries
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackTerminalData decider symbols =
      (directSourceFinalCarrierFallbackRecordGeometries
        decider symbols).flatMap fun geometry =>
          carrierLensRouteTerminalDataBlock
            geometry.horizontal geometry.span := by
  unfold directSourceFinalCarrierFallbackTerminalData
    CarrierFallbackTerminalData.terminalData
  have prefixEq :=
    directSourceFinalCarrierFallbackRecordGeometry_prefixBlocks
      decider symbols
  unfold directSourceFinalCarrierFallbackPrefixBlocks at prefixEq
  rw [← prefixEq]
  rw [List.flatMap_map]
  rfl

/-- The compiler's three carrier query columns consume the same four final
occurrence slots per retained geometry as the declarative record blocks. -/
theorem directSourceFinalCarrierFallbackSemanticQueries_eq_queryBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackSemanticQueries decider symbols =
      CarrierFallbackRouteTailRecords.queryBlocks
        (directSourceFinalCarrierFallbackRecordGeometries decider symbols)
        (directSourceFinalCarrierOccurrenceSlots decider symbols) := by
  unfold directSourceFinalCarrierFallbackSemanticQueries
  rw [directSourceFinalCarrierFallbackTerminalData_eq_geometries]
  exact carrier_alignedQueries_terminalBlocks _ _
    (directSourceFinalCarrierFallbackRecordSlots_length decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
