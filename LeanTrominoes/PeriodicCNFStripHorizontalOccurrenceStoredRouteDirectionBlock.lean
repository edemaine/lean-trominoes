/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteDirectionBlock
import LeanTrominoes.PositionedPeriodicCNFTaggedOccurrenceMembership

/-! # Compact stored routes selected by horizontal occurrences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicOrthocrossing

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- A successful normalized occurrence lookup selects the same clause and
literal indices in the pre-padding routed formula, and hence retrieves one
compact retained-polarity direction block. -/
theorem horizontalOccurrenceStoredRoute_directionBlock_of_lookup
    (input : HorizontalOccurrenceRouteInput)
    (tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence RoutedVariable)
    (lookup : horizontalOccurrenceLookupComputed input = some tagged) :
    ∃ block : HorizontalRoutedRouteDirectionBlock,
      unitSubdivisionDirections
          (horizontalOccurrenceStoredRouteComputed (input, tagged)) =
        block.directions RetainedFigureNineRouteDirectionBlock.directions := by
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
  let normalizedPlacement : PeriodicVariablePlacement RoutedVariable :=
    { period := horizontalPaddedRoutedPeriodComputed source
      position := fun _ => (0, 0) }
  have normalizedClauseMember' :
      (normalizedClause, tagged.2.1) ∈
        (((horizontalRoutedFormulaComputed source).scale 2).anchorNormalize
          normalizedPlacement).clauses.zipIdx := by
    simpa only [horizontalNormalizedRoutedFormulaComputed,
      horizontalPaddedRoutedFormulaComputed, normalizedPlacement] using
      normalizedClauseMember
  rcases
      PositionedPeriodicCNF.exists_source_members_of_scale_anchorNormalize_members
        (horizontalRoutedFormulaComputed source) 2 normalizedPlacement
        normalizedClauseMember' normalizedLiteralMember with
    ⟨sourceClause, sourceLiteral,
      sourceClauseMember, sourceLiteralMember⟩
  rcases horizontalRoutedRoute_directionBlock_of_members
      source sourceClauseMember sourceLiteralMember with
    ⟨block, directionWord⟩
  refine ⟨block, ?_⟩
  simpa only [horizontalOccurrenceStoredRouteComputed,
    horizontalOccurrenceRouteQueryInput, source] using directionWord

end PeriodicCNFStripReduction
end LeanTrominoes

end
