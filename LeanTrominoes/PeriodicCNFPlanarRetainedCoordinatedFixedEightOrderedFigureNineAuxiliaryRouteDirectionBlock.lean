/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSuffixCases
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalDirectionBlock

/-! # Finite blocks for retained auxiliary Figure 9 routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget

local instance auxiliaryRouteDirectionVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Every genuine non-inherited retained Figure 9 incidence normalizes to one
finite local-template direction block. -/
theorem
    retainedOrderedFixedEightFigureNineAuxiliaryRoute_directionBlock
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (notInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        literal.atom ≠ .inl (.inl sourceAtom)) :
    ∃ (metadata :
        PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
          (PeriodicPlanarThreeSATThreeVariable Variable))
        (query :
          PlanarOneInThreeNoUnitsFigureNine.LocalDirectionQuery),
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
        query.1 =
          PeriodicCNF.FormulaShapeOfFormula.clauseProfile
            (PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles
              metadata.sourceClause.literals) ∧
        unitSubdivisionDirections
            (AxisDirection.normalizeOrthogonalPolyline
              (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty clauseIndex literalIndex)) =
          PlanarOneInThreeNoUnitsFigureNine.normalizedLocalDirectionBlock
            query ∧
        ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
          query.1).incidenceAt query.2).clauseIndex =
            metadata.localClauseIndex ∧
        ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
          query.1).incidenceAt query.2).literalIndex = literalIndex := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let clearanceDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have clearanceNonempty :
      ∀ selected ∈ clearanceSource.clauses,
        selected.literals ≠ [] :=
    retainedFigureNineClearancePositionedFormula_clausesNonempty
      source sourceClausesNonempty
  rcases
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_directionBlock_of_members
        clearanceSource clearancePlacement clearanceWidth clearanceDistinct
        clearanceNonempty clauseMember literalMember with
    ⟨metadata, query, metadataLookup, metadataClause, queryProfile,
      localBlock, clauseCoordinate, literalCoordinate⟩
  have rawEq :=
    retainedOrderedFixedEightComposedRawIncidenceRoutes_eq_normalizedLocalRoutes_of_not_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember notInherited
  refine ⟨metadata, query, metadataLookup, metadataClause, queryProfile, ?_,
    clauseCoordinate, literalCoordinate⟩
  rw [rawEq]
  exact localBlock

end PeriodicOrthocrossing
end LeanTrominoes
