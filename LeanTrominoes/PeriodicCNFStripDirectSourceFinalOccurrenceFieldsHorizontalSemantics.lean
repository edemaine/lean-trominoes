/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFrameBlockLengths
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalEndpointDirections
import LeanTrominoes.PeriodicCNFStripHorizontalPresentedOccurrenceFields
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLiteralIndexBlocks
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticPlanarPresentationRoutes

/-! # Direct variable occurrence fields agree with the horizontal source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicPlanarOneInThreeToThreeDM
open HorizontalRoutedRouteHeaderClauseFrame

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance occurrenceFieldsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The completed records retain exactly the kind and polarity of every
actual horizontal literal, in the same clause-major presentation order. -/
theorem directSourceFinalVariableOccurrenceData_literalFields_eq_horizontal
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableOccurrenceData decider symbols).map
        (fun record => (record.kind, record.polarity)) =
      presentedLiteralFields (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  rw [presentedLiteralFields_eq_of_polarityNormalized _
    (horizontalRoutedFormulaComputed_polarityNormalized _)]
  have blockFields :
      (directSourceFinalClauseFrameBlocks decider symbols).map
        (List.map fun frame =>
          (HorizontalRoutedRouteHeader.outputConnectorKind frame.header,
            HorizontalRoutedRouteHeader.outputPolarity frame.header)) =
      (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses.map
          (fun clause => (List.range clause.length).map fun index =>
            (connectorKindOfLiteralIndex index,
              PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity index)) := by
    calc
      _ = (directSourceFinalClauseFrameBlocks decider symbols).map
          (fun block => (List.range block.length).map fun index =>
            (connectorKindOfLiteralIndex index,
              PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity index)) := by
        apply List.map_congr_left
        intro block member
        exact outputBlock_kind_polarity (directSourceFinalClauseDescriptors decider symbols)
          block member
      _ = _ := by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map fun length => (List.range length).map fun index =>
            (connectorKindOfLiteralIndex index,
              PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity index))
            (directSourceFinalClauseFrameBlocks_lengths_eq_horizontalRouted decider symbols)
  have streamFields := congrArg List.flatten blockFields
  rw [← List.map_flatten, directSourceFinalClauseFrameBlocks_flatten,
    List.flatten_eq_flatMap, List.flatMap_map] at streamFields
  have completed : (directSourceFinalVariableOccurrenceData decider symbols).map
        (fun record => (record.kind, record.polarity)) =
      (directSourceFinalCompiledOccurrenceData decider symbols).map
        (fun record => (record.kind, record.polarity)) := by
    rw [directSourceFinalVariableOccurrenceData_eq_routePairs,
      directSourceFinalCompiledOccurrenceData_eq_routePairs]
    simp
  have projected := congrArg
    (List.map fun record : HorizontalRoutedRouteHeader.OccurrenceData => (record.kind, record.polarity))
    (directSourceFinalClauseFrames_map_occurrenceData decider symbols)
  rw [completed]
  calc
    _ = (directSourceFinalClauseFrames decider symbols).map
        (fun frame => (HorizontalRoutedRouteHeader.outputConnectorKind frame.header,
          HorizontalRoutedRouteHeader.outputPolarity frame.header)) := by
      simpa only [List.map_map, Function.comp_def, HorizontalRoutedRouteHeader.occurrenceData] using
        projected.symm
    _ = _ := by simpa only [id_eq] using streamFields

/-- Kind, polarity, and variable-end direction agree jointly with the actual
horizontal occurrences; the three columns refer to the same incidences. -/
theorem directSourceFinalVariableOccurrenceData_fields_eq_horizontal
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableOccurrenceData decider symbols).map
        (fun record => ((record.kind, record.polarity), record.direction)) =
      presentedOccurrenceFields
        (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        (horizontalRoutedRoutesComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols
  let positioned := horizontalRoutedFormulaComputed source
  let routes := horizontalRoutedRoutesComputed source
  let records := directSourceFinalVariableOccurrenceData decider symbols
  let fields := presentedOccurrenceFields positioned routes
  have literals : fields.map Prod.fst = records.map (fun record => (record.kind, record.polarity)) :=
    (presentedOccurrenceFields_map_literalFields positioned routes).trans
      (directSourceFinalVariableOccurrenceData_literalFields_eq_horizontal decider symbols).symm
  have directions : fields.map Prod.snd = records.map HorizontalRoutedRouteHeader.OccurrenceData.direction :=
    (presentedOccurrenceFields_map_directions positioned routes).trans
      (directSourceFinalVariableOccurrenceData_directions_eq_horizontal decider symbols).symm
  have reconstructed := List.zip_of_prod literals directions
  rw [List.zip_map'] at reconstructed
  exact reconstructed.symm

/-- The same complete occurrence fields belong to the padded, normalized
semantic source consumed by the variable ribbon fan construction. -/
theorem directSourceFinalVariableOccurrenceData_fields_eq_normalized
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableOccurrenceData decider symbols).map
        (fun record => ((record.kind, record.polarity), record.direction)) =
      presentedOccurrenceFields
        (horizontalSemanticNormalizedRibbonSource (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        (horizontalSemanticNormalizedPlanarPresentation
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).routes := by
  rw [directSourceFinalVariableOccurrenceData_fields_eq_horizontal,
    horizontalRoutedFormulaComputed_eq_semanticData, horizontalRoutedRoutesComputed_eq_semanticData,
    horizontalSemanticNormalizedPlanarPresentation_routes]
  exact (presentedOccurrenceFields_normalized_scale _ _ _ 2 (by decide)).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
