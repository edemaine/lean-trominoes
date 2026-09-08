/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceColumnBodySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceBodyHorizontalSemantics

/-! # Canonical source entries determine complete variable-incidence columns -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- A coherent local column has the actual source entry's typed body shape. -/
theorem horizontalVariableIncidenceLocalColumn_eq_typedShape
    (source : PeriodicCNF Nat) (entry : RoutedVariable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource source).erase)
    (column : GroupedVariableIncidenceLocalColumn)
    (pairEq : column.pair =
      (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1),
        groupedVariableFanGenericSlot entry.2))
    (bodyEq : column.bodyBlock = incidenceColors.map (fun color => unitSubdivisionDirections
      (horizontalOccurrenceCoordinatedRouteComputed (((source, entry.1), entry.2), color))))
    (kindEq : column.pair.1.kind (groupedVariableFanSiteSlot column.pair.2) = column.data.kind) :
    column.localBodyBlock = groupedVariableIncidenceTypedShapeBodies
      (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2
      (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1))
      (fun color => unitSubdivisionDirections
        (horizontalOccurrenceCoordinatedRouteComputed (((source, entry.1), entry.2), color))) := by
  let active : ActiveOccurrenceEntry (horizontalSemanticNormalizedRibbonSource source).erase :=
    ⟨entry, member⟩
  have fanKind : (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1)).kind
      (occurrenceVariableSiteSlot entry.2) =
      occurrenceConnectorKind (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2 := by
    rw [horizontalOccurrenceVariableRibbonFanDataComputed_eq_semantic source active]
    exact VariableRibbonFanData.sourceVariableRibbonFanData_kind_of_same_atom
      (horizontalSemanticNormalizedPlanarPresentation source) active active rfl
  exact GroupedVariableIncidenceLocalColumn.localBodyBlock_eq_typedShape_of_fields
    (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2 _ _
    column pairEq bodyEq kindEq fanKind

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance columnHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Both semantic projections of every local column belong to the same
canonical source entry, without selecting either column independently. -/
theorem directSourceFinalGroupedVariableIncidenceLocalColumns_fields_horizontal
    (symbols : List encoding.Γ) :
    List.Forall₂ (fun column entry =>
      column.pair =
        (horizontalOccurrenceVariableRibbonFanDataComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1),
          groupedVariableFanGenericSlot entry.2) ∧
      column.bodyBlock = incidenceColors.map (fun color => unitSubdivisionDirections
        (horizontalOccurrenceCoordinatedRouteComputed
          (((PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1), entry.2), color))))
      (directSourceFinalGroupedVariableIncidenceLocalColumns decider symbols)
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase) := by
  have bodyLength := congrArg List.length
    (directSourceFinalGroupedOccurrenceDirectionBodyBlocks_eq_horizontal decider symbols)
  simp only [List.length_map] at bodyLength
  have dataLength := (directSourceFinalGroupedOccurrenceDirectionBodyBlocks_length decider symbols).symm.trans bodyLength
  unfold directSourceFinalGroupedVariableIncidenceLocalColumns
  rw [directSourceFinalGroupedVariableFanSlots_eq_horizontal,
    directSourceFinalGroupedOccurrenceDirectionBodyBlocks_eq_horizontal]
  exact GroupedVariableIncidenceLocalColumn.fieldsAligned_of_maps _ _ _ _ _
    ((directSourceFinalGroupedOccurrenceTripleBlockStarts_length decider symbols).trans dataLength)
    dataLength

/-- The complete local body-block list has the typed shape of the actual
canonical entry list, including every finite prefix and routed RGB suffix. -/
theorem directSourceFinalGroupedVariableIncidenceLocalBodyBlocks_eq_horizontalTypedShape
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableIncidenceLocalColumns decider symbols).map
        GroupedVariableIncidenceLocalColumn.localBodyBlock =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).map fun entry =>
        groupedVariableIncidenceTypedShapeBodies
          (horizontalSemanticNormalizedRibbonSource
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2
          (horizontalOccurrenceVariableRibbonFanDataComputed
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1))
          (fun color => unitSubdivisionDirections (horizontalOccurrenceCoordinatedRouteComputed
            (((PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1), entry.2), color))) := by
  have aligned := (directSourceFinalGroupedVariableIncidenceLocalColumns_fields_horizontal decider symbols).imp_of_mem
    (fun column columnMember entry entryMember fields =>
      horizontalVariableIncidenceLocalColumn_eq_typedShape
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
        entry entryMember column fields.1 fields.2
        (directSourceFinalGroupedVariableIncidenceLocalColumns_valid decider symbols column columnMember).1)
  exact List.map_eq_map_of_forall₂ _ _ aligned

/-- The complete compiled variable-incidence body stream now has its actual
canonical typed shape, with all global body lookups eliminated. -/
theorem directSourceFinalGroupedVariableIncidenceBodies_eq_horizontalTypedShape
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceBodies decider symbols =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).flatMap fun entry =>
        groupedVariableIncidenceTypedShapeBodies
          (horizontalSemanticNormalizedRibbonSource
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2
          (horizontalOccurrenceVariableRibbonFanDataComputed
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1))
          (fun color => unitSubdivisionDirections (horizontalOccurrenceCoordinatedRouteComputed
            (((PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1), entry.2), color))) := by
  exact (directSourceFinalGroupedVariableIncidenceBodies_eq_localColumns decider symbols).trans
    ((congrArg List.flatten
      (directSourceFinalGroupedVariableIncidenceLocalBodyBlocks_eq_horizontalTypedShape decider symbols)).trans
      List.flatMap_def.symm)

end LeanTrominoes.PeriodicCNFStripReduction

end
