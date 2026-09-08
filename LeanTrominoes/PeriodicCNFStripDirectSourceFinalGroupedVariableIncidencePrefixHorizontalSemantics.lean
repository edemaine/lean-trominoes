/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceTypedDirectionBlockSemantics

/-! # Canonical horizontal semantics of all grouped variable prefixes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM
open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance groupedPrefixHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- All compiled finite variable prefixes are the actual horizontal prefixes
in canonical occurrence-entry, typed-triple, and red/green/blue order. -/
theorem directSourceFinalGroupedVariableIncidencePrefixBodies_eq_horizontal
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableIncidencePrefixQueries decider symbols).map
      HorizontalFiniteIncidenceDirectionQuery.directions =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).flatMap
        (fun entry =>
          (occurrenceTriples (horizontalSemanticNormalizedRibbonSource
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase
            entry.1 entry.2).flatMap fun triple =>
              incidenceColors.map fun color => horizontalVariableIncidencePrefixDirections
                (((PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1), triple), color)) := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols
  let positioned := horizontalSemanticNormalizedRibbonSource source
  unfold directSourceFinalGroupedVariableIncidencePrefixQueries
  rw [directSourceFinalGroupedVariableFanSlots_eq_horizontal,
    List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro entry member
  let active : ActiveOccurrenceEntry positioned.erase := ⟨entry, member⟩
  have kindEq : (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1)).kind
      (occurrenceVariableSiteSlot entry.2) =
      occurrenceConnectorKind positioned.erase entry.1 entry.2 := by
    rw [horizontalOccurrenceVariableRibbonFanDataComputed_eq_semantic source active]
    exact VariableRibbonFanData.sourceVariableRibbonFanData_kind_of_same_atom
      (horizontalSemanticNormalizedPlanarPresentation source) active active rfl
  rw [groupedVariableIncidencePrefixBodies_eq_typed positioned.erase entry.1 entry.2 _ kindEq]
  apply List.flatMap_congr
  intro triple _member
  change ([.red, .green, .blue] : List WireColor).map _ =
    ([.red, .green, .blue] : List WireColor).map _
  apply List.map_congr_left
  intro color _member
  exact groupedVariableIncidenceTypedPrefixDirection_eq_horizontal source entry.1 triple color

end LeanTrominoes.PeriodicCNFStripReduction

end
