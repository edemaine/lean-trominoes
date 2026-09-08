/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.ListZipWithFourMappedColumns
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceLocalColumnSemantics
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceLocalTypedShapeSemantics

/-! # Typed shapes of coherent local occurrence columns -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction.GroupedVariableIncidenceLocalColumn

open Gadget PlanarThreeDM PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

/-- Global bodies depend only on the block starts and fan/slot column.
The aligned data and RGB columns may be projected away before flattening. -/
theorem map_globalBodyBlock_zipWith4
    (keys : List Nat) (bodies : List (List AxisDirection))
    (starts : List Nat) (pairs : List GroupedVariableFanSlot)
    (data : List FinalFanOccurrenceData) (blocks : List (List (List AxisDirection)))
    (dataLength : starts.length = data.length)
    (blocksLength : starts.length = blocks.length) :
    ((List.zipWith4 GroupedVariableIncidenceLocalColumn.mk starts pairs data blocks).map
      (globalBodyBlock keys bodies)) =
      List.zipWith (fun start pair =>
        ((groupedVariableIncidencePrefixQueryBlock pair).zipIdx (3 * start)).map fun tagged =>
          HorizontalFiniteIncidenceDirectionQuery.directions tagged.1 ++
            if tagged.2 ∈ keys then
              FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody keys bodies tagged.2
            else []) starts pairs := by
  rw [List.map_zipWith4]
  change List.zipWith4 (fun start pair _ _ =>
      ((groupedVariableIncidencePrefixQueryBlock pair).zipIdx (3 * start)).map fun tagged =>
        HorizontalFiniteIncidenceDirectionQuery.directions tagged.1 ++
          if tagged.2 ∈ keys then
            FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody keys bodies tagged.2
          else []) starts pairs data blocks = _
  rw [List.zipWith4_ignore_fourth_of_length_eq _ starts pairs data blocks blocksLength,
    List.zipWith3_ignore_third_of_length_eq _ starts pairs data dataLength]

/-- The fan/slot and RGB body projections retain their shared source entry. -/
theorem fieldsAligned_of_maps
    {Entry : Type*} (starts : List Nat) (entries : List Entry)
    (data : List FinalFanOccurrenceData)
    (pair : Entry → GroupedVariableFanSlot) (body : Entry → List (List AxisDirection))
    (startsLength : starts.length = entries.length)
    (dataLength : data.length = entries.length) :
    List.Forall₂ (fun column entry => column.pair = pair entry ∧ column.bodyBlock = body entry)
      (List.zipWith4 GroupedVariableIncidenceLocalColumn.mk
        starts (entries.map pair) data (entries.map body)) entries := by
  exact List.forall₂_zipWith4_maps GroupedVariableIncidenceLocalColumn.mk pair body
    (fun column entry => column.pair = pair entry ∧ column.bodyBlock = body entry)
    (fun _ _ _ => ⟨rfl, rfl⟩) starts entries data startsLength dataLength

/-- Coherent finite fields and connector kinds determine the full local
body's typed shape; the absolute block start disappears. -/
theorem localBodyBlock_eq_typedShape_of_fields
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (fan : VariableRibbonFanData) (routedBody : WireColor → List AxisDirection)
    (column : GroupedVariableIncidenceLocalColumn)
    (pairEq : column.pair = (fan, groupedVariableFanGenericSlot slot))
    (bodyEq : column.bodyBlock = incidenceColors.map routedBody)
    (kindEq : column.pair.1.kind (groupedVariableFanSiteSlot column.pair.2) = column.data.kind)
    (fanKind : fan.kind (occurrenceVariableSiteSlot slot) = occurrenceConnectorKind source atom slot) :
    column.localBodyBlock = groupedVariableIncidenceTypedShapeBodies source atom slot fan routedBody := by
  have dataKind : column.data.kind = occurrenceConnectorKind source atom slot := by
    rw [pairEq] at kindEq
    simp only [groupedVariableFanSiteSlot_genericSlot] at kindEq
    exact kindEq.symm.trans fanKind
  unfold localBodyBlock
  rw [pairEq, bodyEq]
  exact groupedVariableIncidenceLocalBodyBlock_eq_typedShape source atom slot fan column.data
    column.start routedBody fanKind dataKind

end LeanTrominoes.PeriodicCNFStripReduction.GroupedVariableIncidenceLocalColumn

end
