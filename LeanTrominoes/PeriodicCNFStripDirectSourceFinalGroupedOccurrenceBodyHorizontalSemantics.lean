/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceBodyHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceLocalColumns

/-! # Complete geometric occurrence bodies in canonical grouped source order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

private theorem zipWith_getD_of_lt
    {First Second Target : Type*}
    (combine : First → Second → Target) (first : List First) (second : List Second)
    (index : Nat) (firstDefault : First) (secondDefault : Second) (fallback : Target)
    (firstLt : index < first.length) (secondLt : index < second.length) :
    (List.zipWith combine first second).getD index fallback =
      combine (first.getD index firstDefault) (second.getD index secondDefault) := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_zipWith]; omega),
    List.getElem_zipWith, List.getD_eq_getElem _ _ firstLt,
    List.getD_eq_getElem _ _ secondLt]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance groupedBodyHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- The actual grouped RGB body blocks are precisely the coordinated
geometric routes of the normalized source's canonical atom/slot entries. -/
theorem directSourceFinalGroupedOccurrenceDirectionBodyBlocks_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceDirectionBodyBlocks decider symbols =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).map
        (fun entry => incidenceColors.map fun color => unitSubdivisionDirections
          (horizontalOccurrenceCoordinatedRouteComputed
            (((PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1), entry.2), color))) := by
  unfold directSourceFinalGroupedOccurrenceDirectionBodyBlocks
  rw [directSourceFinalGroupedOccurrenceIndices_eq_occurrenceEntries, List.map_map]
  apply List.map_congr_left
  intro entry member
  -- Reduce the mapped composition before comparing opaque compiled bodies.
  dsimp only [Function.comp_def]
  obtain ⟨tagged, lookup⟩ := occurrenceAt_exists_of_entry_mem
    (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry member
  have indexMember := List.mem_map_of_mem
    (f := occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase) member
  have indexLt := directSourceFinalGroupedOccurrenceIndex_lt decider symbols _
    ((directSourceFinalGroupedOccurrenceIndices_eq_occurrenceEntries decider symbols).symm ▸ indexMember)
  have frameLt : occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry <
      (directSourceFinalOccurrenceFramesExpected decider symbols).length :=
    lt_of_lt_of_eq indexLt (directSourceFinalOccurrenceFramesExpected_length decider symbols).symm
  have pairLt : occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry <
      (directFigureNinePolarityRoutePairs decider symbols).length :=
    lt_of_lt_of_eq frameLt (directSourceFinalOccurrenceFramesExpected_length_eq_routePairs decider symbols)
  exact (zipWith_getD_of_lt directFinalOccurrenceDirectionBodyBlock
    (directSourceFinalOccurrenceFramesExpected decider symbols)
    (directFigureNinePolarityRoutePairs decider symbols) _ default default [] frameLt pairLt).trans
      (directFinalOccurrenceDirectionBodyBlock_eq_horizontal_of_occurrenceAt
        decider symbols entry member tagged lookup)

end LeanTrominoes.PeriodicCNFStripReduction

end
