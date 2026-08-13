/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineRouteFamily

/-!
# Composed Figure 9 and unit-elimination routes over the retained source

The sequential positioned adapters use a uniform Manhattan connector at
each transformation boundary.  That connector is sufficient for endpoint
and orthogonality certificates, but it can cross another connector inside a
single transformed clause.  The composed finite drawings instead select
explicit noncrossing routes through both transformations at once.

This file instantiates those composed drawings over the normalized retained
fixed-eight source.  It deliberately keeps the unwrapped two-stage variable
type: a later renaming transports these coordinates to the public wrapped
formula without changing any route geometry.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- The raw unit-free exact-one formula obtained by composing Figure 9 and
unit elimination directly over the retained fixed-eight source. -/
def
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PeriodicOneInThreeNoUnitsPositioned.formula
    (PeriodicOneInThreePositioned.formula
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source))

/-- Placement paired with the directly composed raw formula. -/
def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.composedPlacement
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)

private theorem exists_tail_head?_of_length_ge_two
    (route : List Cell)
    (length : 2 ≤ route.length) :
    ∃ exit, route.tail.head? = some exit := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons exit tail => exact ⟨exit, rfl⟩

/-- Original-source suffixes attached to the appropriate boundary point of
each certified composed local drawing. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedOriginalInheritedRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :=
  PlanarOneInThreeNoUnitsFigureNine.inheritedRouteSuffixes
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
      source sourceWidth)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      let valid :=
        retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember
      ⟨valid.1, valid.2.1⟩)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        sourceClauseMember sourceLiteralMember).2.2)
    (fun _sourceClause sourceClauseIndex sourceClauseMember
        _sourceLiteral sourceLiteralIndex sourceLiteralMember => by
      let route :=
        retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source sourceClauseIndex sourceLiteralIndex
      have length : 2 ≤ route.length := by
        simpa [route] using
          retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_length_ge_two
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            sourceClauseMember sourceLiteralMember
      exact exists_tail_head?_of_length_ge_two route length)

/-- Complete raw routes selected from the certified composed local drawings
and the retained normalized source routes. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PlanarOneInThreeNoUnitsFigureNine.splicedRoutes
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
      source sourceWidth)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedOriginalInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Every genuine directly composed raw route has canonical endpoints and
is an orthogonal polyline. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
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
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source)
            clause) ∧
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source)
            clause literal) ∧
      OrthogonalPolyline
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  simpa [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes] using
    PlanarOneInThreeNoUnitsFigureNine.splicedRoutes_valid_of_members
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedOriginalInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
