/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableTriplePositionTable
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonEraseBridge

/-! # Exact variable-triple position tables from finite fan and slot fields -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Gadget PlanarThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

private theorem tripleDecidableEq_eq_ribbon :
    horizontalThreeDMTripleVariableDecidableEq = horizontalRibbonRoutedVariableDecidableEq :=
  Subsingleton.elim _ _

private theorem tripleKind_eq_ribbon (source : PeriodicCNF RoutedVariable)
    (atom : RoutedVariable) (slot : OccurrenceSlot) :
    @occurrenceConnectorKind RoutedVariable horizontalThreeDMTripleVariableDecidableEq source atom slot =
      @occurrenceConnectorKind RoutedVariable horizontalRibbonRoutedVariableDecidableEq source atom slot :=
  congrArg (fun decEq => @occurrenceConnectorKind RoutedVariable decEq source atom slot)
    tripleDecidableEq_eq_ribbon

private theorem triplePolarity_eq_ribbon (source : PeriodicCNF RoutedVariable)
    (atom : RoutedVariable) (slot : OccurrenceSlot) :
    @occurrencePolarity RoutedVariable horizontalThreeDMTripleVariableDecidableEq source atom slot =
      @occurrencePolarity RoutedVariable horizontalRibbonRoutedVariableDecidableEq source atom slot :=
  congrArg (fun decEq => @occurrencePolarity RoutedVariable decEq source atom slot)
    tripleDecidableEq_eq_ribbon

/-- Finite offsets of every triple in the selected variable occurrence module. -/
def groupedVariableTriplePositionTable (pair : GroupedVariableFanSlot) : List Cell :=
  let slot := groupedVariableFanSiteSlot pair.2
  let polarity := pair.1.polarity slot
  match pair.1.kind slot with
  | .fixedRed => allFixedRedTriples.map fun triple =>
      placeVariableModulePoint slot ((FixedRedConnector.boundaryDrawing polarity).triplePosition triple)
  | .fixedGreen => allOrdinaryTriples.map fun triple =>
      placeVariableModulePoint slot ((VariableOccurrence.orientedBoundaryDrawing .fixedGreen polarity).triplePosition triple)
  | .fixedBlue => allOrdinaryTriples.map fun triple =>
      placeVariableModulePoint slot ((VariableOccurrence.orientedBoundaryDrawing .fixedBlue polarity).triplePosition triple)

theorem groupedVariableTriplePositionTable_length_pos (pair : GroupedVariableFanSlot) :
    0 < (groupedVariableTriplePositionTable pair).length := by
  cases kindEq : pair.1.kind (groupedVariableFanSiteSlot pair.2) <;>
    simp [groupedVariableTriplePositionTable, kindEq, allFixedRedTriples, allOrdinaryTriples]

/-- The finite table uses the actual connector kind, polarity and active slot. -/
theorem groupedVariableTriplePositionTable_eq_horizontal
    (source : PeriodicCNF Nat) (entry : RoutedVariable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource source).erase) :
    (groupedVariableTriplePositionTable
      (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1),
        groupedVariableFanGenericSlot entry.2)).map
      (Cell.add (horizontalThreeDMVariableOriginComputed source entry.1)) =
        horizontalThreeDMVariableTriplePositionTableBlockComputed source entry := by
  let positioned := horizontalSemanticNormalizedRibbonSource source
  let active : ActiveOccurrenceEntry positioned.erase := ⟨entry, member⟩
  have kindEq : (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1)).kind
      (occurrenceVariableSiteSlot entry.2) = occurrenceConnectorKind positioned.erase entry.1 entry.2 := by
    rw [horizontalOccurrenceVariableRibbonFanDataComputed_eq_semantic source active]
    exact VariableRibbonFanData.sourceVariableRibbonFanData_kind_of_same_atom
      (horizontalSemanticNormalizedPlanarPresentation source) active active rfl
  have polarityEq : (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1)).polarity
      (occurrenceVariableSiteSlot entry.2) = occurrencePolarity positioned.erase entry.1 entry.2 := by
    rw [horizontalOccurrenceVariableRibbonFanDataComputed_eq_semantic source active]
    exact VariableRibbonFanData.sourceVariableRibbonFanData_polarity_of_same_atom
      (horizontalSemanticNormalizedPlanarPresentation source) active active rfl
  simp only [horizontalThreeDMVariableTriplePositionTableBlockComputed,
    horizontalNormalizedRoutedEraseComputed_eq_semanticData, tripleKind_eq_ribbon, triplePolarity_eq_ribbon]
  unfold groupedVariableTriplePositionTable
  simp only [groupedVariableFanSiteSlot_genericSlot]
  dsimp only [positioned] at kindEq polarityEq
  rw [kindEq, polarityEq]
  cases occurrenceConnectorKind (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2 <;>
    simp only [List.map_map, Function.comp_def, ordinaryTripleSitePositionTable,
      fixedRedTripleSitePositionTable]

private theorem usedOccurrenceSlots_eq_entries (source : PeriodicCNF RoutedVariable) :
    @usedOccurrenceSlots RoutedVariable horizontalThreeDMTripleVariableDecidableEq source =
      @occurrenceEntries RoutedVariable horizontalRibbonRoutedVariableDecidableEq source := by
  exact congrArg (fun decEq => @occurrenceEntries RoutedVariable decEq source)
    tripleDecidableEq_eq_ribbon

/-- Translating these local tables in canonical occurrence-entry order gives
exactly the actual variable-triple prefix. -/
theorem groupedVariableTriplePositionTables_eq_horizontal (source : PeriodicCNF Nat) :
    (occurrenceEntries (horizontalSemanticNormalizedRibbonSource source).erase).flatMap
      (fun entry => (groupedVariableTriplePositionTable
        (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1),
          groupedVariableFanGenericSlot entry.2)).map
        (Cell.add (horizontalThreeDMVariableOriginComputed source entry.1))) =
      horizontalThreeDMVariableTriplePositionsComputed source := by
  rw [horizontalThreeDMVariableTriplePositionsComputed_eq_tableBlocks,
    horizontalThreeDMUsedOccurrenceSlotsComputed]
  simp only [horizontalNormalizedRoutedEraseComputed_eq_semanticData,
    usedOccurrenceSlots_eq_entries]
  apply List.flatMap_congr
  intro entry member
  exact groupedVariableTriplePositionTable_eq_horizontal source entry member

end LeanTrominoes.PeriodicCNFStripReduction
end
