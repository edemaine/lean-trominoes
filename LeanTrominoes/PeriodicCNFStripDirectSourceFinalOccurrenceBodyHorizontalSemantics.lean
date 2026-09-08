/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceFrameHorizontalFields
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStoredWordOccurrenceSemantics
import LeanTrominoes.PeriodicCNFStripDirectFinalOccurrenceEndpointFrameHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceTaggedIndexLookup
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSpecifiedDirectionBlock

/-! # Complete direct colored occurrence bodies agree with actual geometry -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Matching endpoint fields and a stored word determine the complete three
colored geometric routes for any successful occurrence query. -/
theorem directFinalOccurrenceDirectionBodyBlock_eq_horizontal_of_fields
    (frame : DirectFinalOccurrenceFrame.Data)
    (pair : HorizontalRoutedRouteHeaderTail.Header × List AxisDirection)
    (input : HorizontalOccurrenceRouteInput)
    (tagged : TaggedOccurrence RoutedVariable)
    (lookup : horizontalOccurrenceLookupComputed input = some tagged)
    (variableFan : frame.variableFan = horizontalOccurrenceVariableRibbonFanDataComputed input.1)
    (slot : frame.occurrenceSlot = input.2)
    (clauseFields : (frame.clauseFrame.clauseFan, frame.clauseFrame.group) =
      (horizontalOccurrenceClauseRibbonFanDataComputed (input.1.1, tagged.2.1),
        terminalGroupOfLiteralIndex tagged.2.2))
    (storedWord : (HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
        PeriodicOrthocrossing.RetainedFigureNineRouteDirectionBlock.directions =
      unitSubdivisionDirections (horizontalOccurrenceStoredRouteComputed (input, tagged))) :
    directFinalOccurrenceDirectionBodyBlock frame pair =
      incidenceColors.map (fun color => unitSubdivisionDirections
        (horizontalOccurrenceCoordinatedRouteComputed (input, color))) := by
  have clauseFan := congrArg Prod.fst clauseFields
  have group := congrArg Prod.snd clauseFields
  dsimp only at clauseFan group
  have clauseIndex := horizontalOccurrenceClauseIndexComputed_eq_of_lookup input tagged lookup
  have terminalGroup := horizontalOccurrenceClauseTerminalGroupComputed_eq_of_lookup input tagged lookup
  unfold directFinalOccurrenceDirectionBodyBlock
  apply List.map_congr_left
  intro color _colorMember
  have clauseFanEq : frame.clauseFrame.clauseFan =
      horizontalOccurrenceClauseRibbonFanDataComputed
        (horizontalOccurrenceClauseRibbonFanQueryComputed (input, color)) := by
    simpa only [horizontalOccurrenceClauseRibbonFanQueryComputed, clauseIndex] using clauseFan
  have groupEq : frame.clauseFrame.group = horizontalOccurrenceClauseTerminalGroupComputed input :=
    group.trans terminalGroup.symm
  have rendered := DirectFinalOccurrenceEndpointFrame.output_routedTokens_eq_horizontal
    frame (input, color) (HorizontalRoutedRouteHeader.block pair.1 pair.2)
    variableFan slot clauseFanEq groupEq
  exact rendered.trans
    (horizontalOccurrenceCoordinatedRoute_directionBlock_eq_of_lookup
      (input, color) tagged lookup _ storedWord).symm

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance occurrenceBodyHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- At the presentation position recovered from a source entry, the actual
compiled frame and header/tail pair render precisely that entry's three
coordinated geometric routes, in red/green/blue order. -/
theorem directFinalOccurrenceDirectionBodyBlock_eq_horizontal_of_occurrenceAt
    (symbols : List encoding.Γ) (entry : RoutedVariable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase)
    (tagged : TaggedOccurrence RoutedVariable)
    (lookup : occurrenceAt (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2 = some tagged) :
    let index : Nat := occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry
    directFinalOccurrenceDirectionBodyBlock
        ((directSourceFinalOccurrenceFramesExpected decider symbols).getD index default)
        ((directFigureNinePolarityRoutePairs decider symbols).getD index default) =
      incidenceColors.map (fun color => unitSubdivisionDirections
        (horizontalOccurrenceCoordinatedRouteComputed
          (((PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1), entry.2), color))) := by
  have fields := directSourceFinalOccurrenceFrame_fields_of_occurrenceAt decider symbols entry member tagged lookup
  dsimp only at fields
  have computedLookup := horizontalOccurrenceLookupComputed_eq_of_semanticLookup
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) entry.1 entry.2 tagged lookup
  dsimp only
  -- Explicit terms avoid expanding the source compiler during clause-fan conversion.
  apply directFinalOccurrenceDirectionBodyBlock_eq_horizontal_of_fields
    ((directSourceFinalOccurrenceFramesExpected decider symbols).getD
      (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry) default)
    ((directFigureNinePolarityRoutePairs decider symbols).getD
      (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry) default)
    ((PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1), entry.2)
    tagged computedLookup fields.1 fields.2.1 fields.2.2
  have selected := directFigureNinePolarityRoutePair_directions_of_occurrenceAt decider symbols
    entry.1 entry.2 tagged lookup
  dsimp only at selected
  simpa only [horizontalOccurrenceStoredRouteComputed, horizontalOccurrenceRouteQueryInput] using selected

end LeanTrominoes.PeriodicCNFStripReduction

end
