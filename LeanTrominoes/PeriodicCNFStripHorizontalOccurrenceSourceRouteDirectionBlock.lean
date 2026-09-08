/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionNormalization
import LeanTrominoes.GadgetSparseRouteDirectionReversal
import LeanTrominoes.GadgetSparseRouteDirectionScalingCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonSourceBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceStoredRouteDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticPlanarPresentationRoutes
import LeanTrominoes.PositionedPeriodicCNFPresentationCanonicalRoutes

/-! # Compact variable-to-clause horizontal source routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicOrthocrossing

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Interpret one compact stored block after the horizontal construction's
factor-two padding and reversal into variable-to-clause orientation. -/
def horizontalOccurrenceSourceDirections
    (block : HorizontalRoutedRouteDirectionBlock) :
    List AxisDirection :=
  reverseDirections
    (repeatDirections 2
      (block.directions
        RetainedFigureNineRouteDirectionBlock.directions))

/-- The exact source word selected by a genuine occurrence lookup is the
factor-two stored word reversed into variable-to-clause orientation. -/
theorem horizontalOccurrenceUnitSourceRoute_directions_of_lookup
    (input : HorizontalOccurrenceRouteInput)
    (tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence RoutedVariable)
    (lookup : horizontalOccurrenceLookupComputed input = some tagged) :
    unitSubdivisionDirections (horizontalOccurrenceUnitSourceRouteComputed input) =
      reverseDirections (repeatDirections 2
        (unitSubdivisionDirections (horizontalOccurrenceStoredRouteComputed (input, tagged)))) := by
  let source := input.1.1
  have occurrenceLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (horizontalNormalizedRoutedFormulaComputed source).erase
          input.1.2 input.2 = some tagged := by
    simpa only [horizontalOccurrenceLookupComputed,
      horizontalOccurrenceLookupInput,
      PeriodicPlanarOneInThreeToThreeDM.occurrenceAt, source] using lookup
  have taggedMember :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals
        (horizontalNormalizedRoutedFormulaComputed source).erase :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      (horizontalNormalizedRoutedFormulaComputed source).erase
      input.1.2 input.2 tagged occurrenceLookup).1
  rcases PositionedPeriodicCNF.exists_members_of_taggedLiterals_mem
      (horizontalNormalizedRoutedFormulaComputed source)
      tagged taggedMember with
    ⟨normalizedClause, normalizedLiteral,
      normalizedClauseMember, normalizedLiteralMember⟩
  have semanticClauseMember :
      (normalizedClause, tagged.2.1) ∈
        (horizontalSemanticNormalizedRibbonSource source).clauses.zipIdx := by
    rw [← horizontalNormalizedRoutedFormulaComputed_eq_semanticData]
    exact normalizedClauseMember
  let planar := horizontalSemanticNormalizedPlanarPresentation source
  have scaledSemanticOrthogonal :
      OrthogonalPolyline
        (scalePolyline 2
          (horizontalSemanticRoutedRoutes source
            tagged.2.1 tagged.2.2)) := by
    have orthogonal :=
      planar.canonicalOrthogonalRoutes.orthogonal
        normalizedClause tagged.2.1 semanticClauseMember
        normalizedLiteral tagged.2.2 normalizedLiteralMember
    simp only [planar,
      PositionedPeriodicCNF.PlanarIncidencePresentation.canonicalOrthogonalRoutes,
      horizontalSemanticNormalizedPlanarPresentation_routes,
      PositionedPeriodicCNF.scaleIncidenceRoutes_apply] at orthogonal
    rw [show (↑(2 : Nat) : Int) = (2 : Int) by decide] at orthogonal
    exact orthogonal
  have scaledStoredOrthogonal :
      OrthogonalPolyline
        (scalePolyline 2
          (horizontalOccurrenceStoredRouteComputed (input, tagged))) := by
    simpa only [horizontalOccurrenceStoredRouteComputed,
      horizontalOccurrenceRouteQueryInput,
      horizontalRoutedRoutesComputed_eq_semanticData, source] using
      scaledSemanticOrthogonal
  have sourceSomeOrthogonal :
      OrthogonalPolyline
        (horizontalOccurrenceSourceRouteSomeComputed (input, tagged)) := by
    unfold horizontalOccurrenceSourceRouteSomeComputed
      horizontalOccurrenceReversedRouteComputed
      horizontalOccurrenceScaledRouteComputed
    exact scaledStoredOrthogonal.reverse.translate _
  have sourceRouteEq :
      horizontalOccurrenceSourceRouteComputed input =
        horizontalOccurrenceSourceRouteSomeComputed (input, tagged) := by
    simp [horizontalOccurrenceSourceRouteComputed, lookup]
  unfold horizontalOccurrenceUnitSourceRouteComputed
  rw [sourceRouteEq]
  rw [unitSubdivisionDirections_unitSubdividePolyline
    _ sourceSomeOrthogonal]
  unfold horizontalOccurrenceSourceRouteSomeComputed
    horizontalOccurrenceReversedRouteComputed
    horizontalOccurrenceScaledRouteComputed
  rw [unitSubdivisionDirections_translatePolyline]
  rw [unitSubdivisionDirections_reverse _ scaledStoredOrthogonal]
  rw [← show (↑(2 : Nat) : Int) = (2 : Int) by decide]
  rw [unitSubdivisionDirections_scalePolyline 2 (by decide)]

/-- Every successful horizontal occurrence lookup has a compact complete
variable-to-clause unit-source direction word. -/
theorem horizontalOccurrenceUnitSourceRoute_directionBlock_of_lookup
    (input : HorizontalOccurrenceRouteInput)
    (tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence RoutedVariable)
    (lookup : horizontalOccurrenceLookupComputed input = some tagged) :
    ∃ block : HorizontalRoutedRouteDirectionBlock,
      unitSubdivisionDirections
          (horizontalOccurrenceUnitSourceRouteComputed input) =
        horizontalOccurrenceSourceDirections block := by
  rcases horizontalOccurrenceStoredRoute_directionBlock_of_lookup input tagged lookup with
    ⟨block, storedDirections⟩
  have exactWord := horizontalOccurrenceUnitSourceRoute_directions_of_lookup input tagged lookup
  rw [storedDirections] at exactWord
  exact ⟨block, exactWord⟩

end PeriodicCNFStripReduction
end LeanTrominoes

end
