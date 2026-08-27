/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRouteGeometry
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRouteDirectionBlock
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityRoutedRoutesComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteDirectionBlock

/-! # Compact direction blocks after retained polarity normalization -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget

local instance retainedPolarityRouteDirectionBlockVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The compact retained-route vocabulary after the four possible stream
operations introduced by routed polarity normalization. -/
abbrev RetainedPolarityRouteDirectionBlock :=
  PeriodicOneInThreePolarityNormalizationRouteSubdivision.RouteDirectionBlock
    RetainedFigureNineRouteDirectionBlock

/-- Every retained routed-polarity occurrence has a compact direction word:
one Figure 9 source block followed by one of the four fixed polarity stream
operations. -/
theorem
    retainedOrderedFixedEightPolarityNormalizedRoute_directionBlock_of_members
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {outputClause : PositionedPeriodicClause
      (PolarityNormalizedVariable
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {outputClauseIndex : Nat}
    (outputClauseMember :
      (outputClause, outputClauseIndex) ∈
        (retainedOrderedFixedEightPolarityNormalizedPositionedFormulaComputed
          source).clauses.zipIdx)
    {outputLiteral : PeriodicLiteral
      (PolarityNormalizedVariable
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {outputLiteralIndex : Nat}
    (outputLiteralMember :
      (outputLiteral, outputLiteralIndex) ∈
        outputClause.literals.zipIdx) :
    ∃ block : RetainedPolarityRouteDirectionBlock,
      unitSubdivisionDirections
          (retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed
            source outputClauseIndex outputLiteralIndex) =
        block.directions RetainedFigureNineRouteDirectionBlock.directions := by
  apply
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.route_directionBlock_of_members
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
        source)
      RetainedFigureNineRouteDirectionBlock.directions
  · intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    exact
      retainedOrderedFixedEightFinalGaugedComputedRoute_directionBlock_of_members
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
        sourceClauseMember sourceLiteralMember
  · intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    exact
      retainedOrderedFixedEightFinalGaugedComputedRoute_geometry_of_members
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
        sourceClauseMember sourceLiteralMember
  · exact outputClauseMember
  · exact outputLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
