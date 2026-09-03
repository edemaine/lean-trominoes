/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineAuxiliaryRouteDirectionBlock
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineInheritedRouteDirectionBlock

/-! # Direction blocks for all named retained Figure 9 routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget

/-- The two compact forms of a retained Figure 9 route word.  Auxiliary
routes use only a finite local block.  Inherited routes append a uniformly
repeated source-tail word to a finite local-plus-connector block. -/
inductive RetainedFigureNineRouteDirectionBlock where
  | local
      (query :
        PlanarOneInThreeNoUnitsFigureNine.LocalDirectionQuery)
  | inherited
      (query :
        PlanarOneInThreeNoUnitsFigureNine.LocalExtendedDirectionQuery)
      (sourceTailDirections : List AxisDirection)

/-- Expand one compact retained Figure 9 route block to its direction word. -/
def RetainedFigureNineRouteDirectionBlock.directions :
    RetainedFigureNineRouteDirectionBlock → List AxisDirection
  | .local query =>
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalDirectionBlock query
  | .inherited query sourceTailDirections =>
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalExtendedDirectionBlock
          query ++
        repeatDirections 144 sourceTailDirections

/-- The common finite-template local query retained by either compact route
block form. -/
def RetainedFigureNineRouteDirectionBlock.localQuery :
    RetainedFigureNineRouteDirectionBlock →
      PlanarOneInThreeNoUnitsFigureNine.LocalDirectionQuery
  | .local query => query
  | .inherited query _ => ⟨query.1, query.2.1⟩

local instance completeRouteDirectionBlockVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Every genuine named retained Figure 9 route has one of the two compact
direction-block forms. -/
theorem
    retainedOrderedFixedEightFigureNineRoute_directionBlock_of_members
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ block : RetainedFigureNineRouteDirectionBlock,
      unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty clauseIndex literalIndex)) =
        block.directions := by
  rcases atomEq : literal.atom with outerInherited | unitAuxiliary
  · rcases figureAtomEq : outerInherited with sourceAtom | figureAuxiliary
    · have literalSource : literal.atom = .inl (.inl sourceAtom) := by
        simp [atomEq, figureAtomEq]
      rcases
        retainedOrderedFixedEightFigureNineInheritedRoute_directionBlock
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember
            sourceAtom literalSource with
        ⟨_data, _first, second, rest, query, _dataLookup, _routeEq,
          directionWord, _clauseCoordinate, _literalCoordinate⟩
      refine ⟨.inherited query
        (unitSubdivisionDirections (second :: rest)), ?_⟩
      simpa [RetainedFigureNineRouteDirectionBlock.directions] using
        directionWord
    · have notInherited :
          ∀ sourceAtom :
              ThreeOccurrenceVariable
                (WrappedPeriodicPlanarSATVariable Variable),
            literal.atom ≠ .inl (.inl sourceAtom) := by
        intro sourceAtom equal
        simp [atomEq, figureAtomEq] at equal
      rcases
          retainedOrderedFixedEightFigureNineAuxiliaryRoute_directionBlock
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember notInherited with
        ⟨_metadata, query, _metadataLookup, _metadataClause,
          directionWord, _clauseCoordinate, _literalCoordinate⟩
      refine ⟨.local query, ?_⟩
      simpa [RetainedFigureNineRouteDirectionBlock.directions] using
        directionWord
  · have notInherited :
        ∀ sourceAtom :
            ThreeOccurrenceVariable
              (WrappedPeriodicPlanarSATVariable Variable),
          literal.atom ≠ .inl (.inl sourceAtom) := by
      intro sourceAtom equal
      simp [atomEq] at equal
    rcases
        retainedOrderedFixedEightFigureNineAuxiliaryRoute_directionBlock
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember literalMember notInherited with
      ⟨_metadata, query, _metadataLookup, _metadataClause,
        directionWord, _clauseCoordinate, _literalCoordinate⟩
    refine ⟨.local query, ?_⟩
    simpa [RetainedFigureNineRouteDirectionBlock.directions] using
      directionWord

end PeriodicOrthocrossing
end LeanTrominoes
