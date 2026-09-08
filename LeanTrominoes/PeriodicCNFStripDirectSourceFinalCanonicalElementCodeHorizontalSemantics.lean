/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripTypedElementCodes
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceKeyHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceBodyHorizontalSemantics

/-! # Compiled element codes name the actual typed horizontal elements -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The finite variable-element selector uses the same tags as the typed
source at each genuine occurrence. -/
theorem horizontalVariableElementCodeBlock_eq_typed
    (source : PeriodicCNF Nat) (entry : RoutedVariable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) (key : Nat) :
    directSourceFinalVariableElementCodeBlock color
        (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1),
          groupedVariableFanGenericSlot entry.2) key =
      TypedElementCode.variableBlock key color
        (occurrenceConnectorKind (horizontalSemanticNormalizedRibbonSource source).erase
          entry.1 entry.2) := by
  let active : ActiveOccurrenceEntry (horizontalSemanticNormalizedRibbonSource source).erase :=
    ⟨entry, member⟩
  have fanKind : (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1)).kind
      (occurrenceVariableSiteSlot entry.2) =
      occurrenceConnectorKind (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2 := by
    rw [horizontalOccurrenceVariableRibbonFanDataComputed_eq_semantic source active]
    exact VariableRibbonFanData.sourceVariableRibbonFanData_kind_of_same_atom
      (horizontalSemanticNormalizedPlanarPresentation source) active active rfl
  unfold directSourceFinalVariableElementCodeBlock
  simp only [groupedVariableFanSiteSlot_genericSlot]
  rw [fanKind]
  cases color <;>
    cases occurrenceConnectorKind (horizontalSemanticNormalizedRibbonSource source).erase
      entry.1 entry.2 <;> rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Actual source entries determine the complete compiled variable-element
code prefix, with each code using its own occurrence key. -/
theorem directSourceFinalCanonicalVariableElementCodes_eq_horizontalBlocks
    (color : WireColor) (symbols : List encoding.Γ) :
    directSourceFinalCanonicalVariableElementCodes decider color symbols =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).flatMap
        (fun entry => TypedElementCode.variableBlock
          (directSourceFinalHorizontalOccurrenceKey decider symbols entry) color
          (occurrenceConnectorKind (horizontalSemanticNormalizedRibbonSource
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2)) := by
  rw [directSourceFinalCanonicalVariableElementCodes_eq_zipWith,
    directSourceFinalGroupedVariableFanSlots_eq_horizontal,
    directSourceFinalUniqueFanQueryKeys_eq_horizontal,
    List.zipWith_map, List.zipWith_self, ← List.flatMap_def]
  apply List.flatMap_congr
  intro entry member
  exact horizontalVariableElementCodeBlock_eq_typed
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) entry member color _

/-- Clause elements use their actual normalized clause positions. -/
theorem directSourceFinalClauseElementCodes_eq_horizontalBlocks
    (color : WireColor) (symbols : List encoding.Γ) :
    directSourceFinalClauseElementCodes decider color symbols =
      (List.range (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses.length).flatMap
        (fun index => TypedElementCode.clauseBlock index color) := by
  rw [directSourceFinalClauseElementCodes_eq_flatMap]
  have countEq : (directSourceFinalClauseIndexPlaceholders decider symbols).length =
      (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses.length := by
    unfold directSourceFinalClauseIndexPlaceholders FiniteUnaryFieldBlockMap.values
    unfold directSourceFinalClauseIndexPlaceholderBlock
    rw [← List.map_eq_flatMap, List.length_map]
    rw [directSourceFinalClauseFans_length_eq_horizontalTypedClauses]
    unfold horizontalThreeDMTypedSourceComputed
    rw [horizontalNormalizedRoutedFormulaComputed_eq_semanticData]
  rw [countEq]
  apply List.flatMap_congr
  intro index _
  cases color <;> rfl

/-- Each complete compiled color column is precisely the structural coding
of its actual typed horizontal element enumeration. -/
theorem directSourceFinalOneColorElementCodes_eq_horizontalTyped
    (color : WireColor) (symbols : List encoding.Γ) :
    directSourceFinalOneColorElementCodes decider color symbols =
      TypedElementCode.elements (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase
        (directSourceFinalHorizontalOccurrenceKey decider symbols) color := by
  unfold directSourceFinalOneColorElementCodes
  rw [TypedElementCode.elements_eq_blocks,
    directSourceFinalCanonicalVariableElementCodes_eq_horizontalBlocks,
    directSourceFinalClauseElementCodes_eq_horizontalBlocks]


/-- The complete compiled code list retains typed color-major order. -/
theorem directSourceFinalCanonicalElementCodes_eq_horizontalTyped
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalElementCodes decider symbols =
      PeriodicThreeDM.incidenceColors.flatMap (TypedElementCode.elements
        (horizontalSemanticNormalizedRibbonSource
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase
        (directSourceFinalHorizontalOccurrenceKey decider symbols)) := by
  unfold directSourceFinalCanonicalElementCodes directSourceFinalGreenBlueElementCodes
  rw [directSourceFinalOneColorElementCodes_eq_horizontalTyped,
    directSourceFinalOneColorElementCodes_eq_horizontalTyped,
    directSourceFinalOneColorElementCodes_eq_horizontalTyped]
  simp only [PeriodicThreeDM.incidenceColors, List.flatMap_cons, List.flatMap_nil, List.append_nil]

end LeanTrominoes.PeriodicCNFStripReduction

end
