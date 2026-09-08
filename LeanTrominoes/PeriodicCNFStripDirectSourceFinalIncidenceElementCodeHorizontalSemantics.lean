/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripVariableIncidenceTypedElementCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalNextOccurrenceKeyHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalParentIndexHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceElementCodeHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeOccurrenceBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceElementCodeCompiler

/-! # Complete incidence-code agreement with actual horizontal typed references -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

private theorem zipWith4_maps {Entry First Second Third Fourth Result : Type*}
    (combine : First → Second → Third → Fourth → Result)
    (first : Entry → First) (second : Entry → Second)
    (third : Entry → Third) (fourth : Entry → Fourth) (entries : List Entry) :
    List.zipWith4 combine (entries.map first) (entries.map second)
        (entries.map third) (entries.map fourth) =
      entries.map (fun entry => combine (first entry) (second entry) (third entry) (fourth entry)) := by
  induction entries with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.map_cons, List.zipWith4, induction]

/-- The actual horizontal fan supplies every premise of finite selector
correctness at its own active source entry. -/
theorem horizontalVariableIncidenceElementCodeBlock_eq_typed
    (source : PeriodicCNF Nat) (entry : RoutedVariable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource source).erase)
    (key : RoutedVariable × OccurrenceSlot → Nat) :
    groupedVariableIncidenceElementCodeBlock
        (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1),
          groupedVariableFanGenericSlot entry.2)
        (key entry)
        (key (entry.1, nextUsedSlot (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2))
        (occurrenceClauseIndex (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2) =
      (occurrenceTriples (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2).flatMap
        (fun triple => incidenceColors.map fun color => TypedElementCode.reference key
          (tripleReferences (horizontalSemanticNormalizedRibbonSource source).erase triple) color) := by
  let active : ActiveOccurrenceEntry (horizontalSemanticNormalizedRibbonSource source).erase :=
    ⟨entry, member⟩
  rw [horizontalOccurrenceVariableRibbonFanDataComputed_eq_semantic source active]
  exact groupedVariableIncidenceElementCodeBlock_eq_typed
    (horizontalSemanticNormalizedRibbonSource source).erase entry.1 active.atom_mem entry.2 active.slot_mem
    _ (VariableRibbonFanData.sourceVariableRibbonFanData_count
      (horizontalSemanticNormalizedPlanarPresentation source) active)
    (VariableRibbonFanData.sourceVariableRibbonFanData_kind_of_same_atom
      (horizontalSemanticNormalizedPlanarPresentation source) active active rfl)
    (VariableRibbonFanData.sourceVariableRibbonFanData_polarity_of_same_atom
      (horizontalSemanticNormalizedPlanarPresentation source) active active rfl) key

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Compiled variable incidences refer to the actual typed elements in
canonical variable-triple and red/green/blue order. -/
theorem directSourceFinalVariableIncidenceElementCodes_eq_horizontalTyped
    (symbols : List encoding.Γ) :
    directSourceFinalVariableIncidenceElementCodes decider symbols =
      (variableTriples (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).flatMap
        (fun triple => incidenceColors.map fun color => TypedElementCode.reference
          (directSourceFinalHorizontalOccurrenceKey decider symbols)
          (tripleReferences (horizontalSemanticNormalizedRibbonSource
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase triple) color) := by
  rw [directSourceFinalVariableIncidenceElementCodes_eq_occurrenceBlocks,
    directSourceFinalGroupedVariableFanSlots_eq_horizontal,
    directSourceFinalUniqueFanQueryKeys_eq_horizontal,
    directSourceFinalGroupedNextOccurrenceKeys_eq_horizontal,
    directSourceFinalGroupedParentIndices_eq_horizontal, zipWith4_maps,
    ← List.flatMap_def, variableTriples_eq_occurrenceEntries_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro entry member
  exact horizontalVariableIncidenceElementCodeBlock_eq_typed
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) entry member
    (directSourceFinalHorizontalOccurrenceKey decider symbols)

/-- The complete emitted incidence-code column is the structural coding of
all actual typed references, aligned with the already verified direction bodies. -/
theorem directSourceFinalCanonicalIncidenceElementCodes_eq_horizontalTyped
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalIncidenceElementCodes decider symbols =
      (triples (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).flatMap
        (fun triple => incidenceColors.map fun color => TypedElementCode.reference
          (directSourceFinalHorizontalOccurrenceKey decider symbols)
          (tripleReferences (horizontalSemanticNormalizedRibbonSource
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase triple) color) := by
  unfold directSourceFinalCanonicalIncidenceElementCodes PeriodicPlanarOneInThreeToThreeDM.triples
  rw [directSourceFinalVariableIncidenceElementCodes_eq_horizontalTyped,
    directSourceFinalClauseIncidenceElementCodes_eq_horizontalTyped decider symbols
      (directSourceFinalHorizontalOccurrenceKey decider symbols), List.flatMap_append]

end LeanTrominoes.PeriodicCNFStripReduction

end
