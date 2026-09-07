/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalSourceWords
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationExactRouteDirectionBlockGeometry
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRouteGeometry
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaBridge
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesBridge
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceDirectionBodyBlockSemantics

/-! # Direct route words equal the complete geometric polarity presentation -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing
open Gadget
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance presentedWordsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance presentedWordsVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every genuine direct final-gauged incidence has the geometry required
by the exact polarity direction-word theorem. -/
theorem directSourceFinalGaugedIncidenceRoutes_geometry_of_members
    (symbols : List encoding.Γ)
    {clause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember : (clause, clauseIndex) ∈
      (directSourceFinalGaugedFormula decider symbols).clauses.zipIdx)
    {literal : PeriodicLiteral
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember : (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤ (directSourceFinalGaugedIncidenceRoutes decider symbols clauseIndex literalIndex).length ∧
      OrthogonalPolyline
        (directSourceFinalGaugedIncidenceRoutes decider symbols clauseIndex literalIndex) := by
  have sourceLocal : (directSourceFormula decider symbols).IsLocal :=
    sourceFormula_isLocal (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have sourceWidth : (directSourceFormula decider symbols).WidthAtMost 3 :=
    sourceFormula_widthAtMostThree (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have sourceOccurrences :
      @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
        (by infer_instance) 3 (directSourceFormula decider symbols) := by
    exact PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3 _
      (sourceFormula_occurrencesAtMostThree (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
  have sourceNonempty : ∀ clause ∈ (directSourceFormula decider symbols).clauses, clause ≠ [] :=
    sourceFormula_clausesNonempty (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have computedMember : (clause, clauseIndex) ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
        (directSourceFormula decider symbols)).clauses.zipIdx := by
    rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq
      (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty]
    exact clauseMember
  have geometry := retainedOrderedFixedEightFinalGaugedComputedRoute_geometry_of_members
    (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty
    computedMember literalMember
  simpa only [directSourceFinalGaugedIncidenceRoutes,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_eq
      (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty]
    using geometry

/-- The direct executable direction blocks equal the actual routed polarity
normalization words in the complete clause-major, literal-minor order. -/
theorem directFigureNinePolarityRoutePairs_map_directions_eq_presented
    (symbols : List encoding.Γ) :
    (directFigureNinePolarityRoutePairs decider symbols).map
        (fun pair => (HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
          RetainedFigureNineRouteDirectionBlock.directions) =
      presentedIncidenceDirectionWords
        (formula (directSourceFinalGaugedFormula decider symbols)
          (directSourceFinalGaugedPlacement decider symbols)
          (directSourceFinalGaugedIncidenceRoutes decider symbols))
        (incidenceRoutes (directSourceFinalGaugedFormula decider symbols)
          (directSourceFinalGaugedPlacement decider symbols)
          (directSourceFinalGaugedIncidenceRoutes decider symbols)) := by
  rw [directFigureNinePolarityRoutePairs_map_directions_eq_exactMetadata]
  exact (presentedIncidenceDirectionWords_formula_eq_exactMetadataRouteBlocks_of_members
    (directSourceFinalGaugedFormula decider symbols)
    (directSourceFinalGaugedPlacement decider symbols)
    (directSourceFinalGaugedIncidenceRoutes decider symbols)
    (directSourceFinalGaugedIncidenceRoutes_geometry_of_members decider symbols)).symm

/-- The direct word list is the actual executable horizontal routed source,
in its clause-major, literal-minor incidence order. -/
theorem directFigureNinePolarityRoutePairs_map_directions_eq_horizontal
    (symbols : List encoding.Γ) :
    (directFigureNinePolarityRoutePairs decider symbols).map
        (fun pair => (HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
          RetainedFigureNineRouteDirectionBlock.directions) =
      presentedIncidenceDirectionWords
        (horizontalRoutedFormulaComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        (horizontalRoutedRoutesComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  rw [horizontalRoutedFormulaComputed_eq_semantic,
    horizontalRoutedRoutesComputed_eq_semantic]
  exact directFigureNinePolarityRoutePairs_map_directions_eq_presented decider symbols

/-- Render the three colored occurrence bodies directly from a source
direction word and the finite endpoint frame. -/
def directFinalOccurrenceDirectionBodyBlockOfDirections
    (frame : DirectFinalOccurrenceFrame.Data)
    (directions : List AxisDirection) : List (List AxisDirection) :=
  PeriodicThreeDM.incidenceColors.map fun color =>
    let endpoint := DirectFinalOccurrenceEndpointFrame.ofColor frame color
    HorizontalOccurrenceDirectionRequest.requestedOutput
      endpoint.leading endpoint.lane
      (reverseDirections (repeatDirections 2 directions)) endpoint.trailing

theorem directFinalOccurrenceDirectionBodyBlock_eq_ofDirections
    (frame : DirectFinalOccurrenceFrame.Data)
    (pair : HorizontalRoutedRouteHeaderTail.Header × List AxisDirection) :
    directFinalOccurrenceDirectionBodyBlock frame pair =
      directFinalOccurrenceDirectionBodyBlockOfDirections frame
        ((HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
          RetainedFigureNineRouteDirectionBlock.directions) := by
  simp only [directFinalOccurrenceDirectionBodyBlock,
    directFinalOccurrenceDirectionBodyBlockOfDirections,
    DirectFinalOccurrenceEndpointFrame.routedTokens,
    HorizontalOccurrenceRoutedRequest.output_tokens,
    horizontalOccurrenceSourceDirections]

private theorem zipWith_occurrenceDirectionBodyBlock
    (frames : List DirectFinalOccurrenceFrame.Data)
    (pairs : List (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection)) :
    List.zipWith directFinalOccurrenceDirectionBodyBlock frames pairs =
      List.zipWith directFinalOccurrenceDirectionBodyBlockOfDirections frames
        (pairs.map fun pair =>
          (HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
            RetainedFigureNineRouteDirectionBlock.directions) := by
  induction frames generalizing pairs with
  | nil => rfl
  | cons frame frames induction =>
      cases pairs with
      | nil => rfl
      | cons pair pairs =>
          simp only [List.zipWith_cons_cons, List.map_cons,
            directFinalOccurrenceDirectionBodyBlock_eq_ofDirections, induction]

/-- The colored occurrence compiler consumes the actual horizontal route
words in order, surrounded by its compiled finite endpoint frames. -/
theorem directSourceFinalColoredOccurrenceDirectionBodies_eq_horizontalRouteWords
    (symbols : List encoding.Γ) :
    directSourceFinalColoredOccurrenceDirectionBodies decider symbols =
      (List.zipWith directFinalOccurrenceDirectionBodyBlockOfDirections
        (directSourceFinalOccurrenceFramesExpected decider symbols)
        (presentedIncidenceDirectionWords
          (horizontalRoutedFormulaComputed
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
          (horizontalRoutedRoutesComputed
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)))).flatten := by
  rw [directSourceFinalColoredOccurrenceDirectionBodies_eq_occurrenceBlocks,
    zipWith_occurrenceDirectionBodyBlock,
    directFigureNinePolarityRoutePairs_map_directions_eq_horizontal]

end LeanTrominoes.PeriodicCNFStripReduction

end
