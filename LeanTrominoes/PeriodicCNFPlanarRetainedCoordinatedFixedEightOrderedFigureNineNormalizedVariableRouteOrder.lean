/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineInheritedEndpointIsolation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedRoutes
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineVariableRouteOrder
import LeanTrominoes.PeriodicGridDrawingLoopErasureRouteOrders

/-!
# Variable route order after final Figure 9 loop erasure

Only twice-inherited atoms can have three occurrences in the final formula.
For each of their routes, variable-endpoint isolation makes orthogonal loop
erasure preserve the terminal direction.  The raw clockwise occurrence order
therefore transfers unchanged to the normalized route family.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 4000000

local instance normalizedVariableOrderVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem two_le_length_of_polylineLastDirection_isGenuine
    {route : List Cell}
    (genuine :
      (AxisDirection.polylineLastDirection route).IsGenuine) :
    2 ≤ route.length := by
  cases route with
  | nil =>
      simp [AxisDirection.polylineLastDirection,
        AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine, AxisDirection.opposite] at genuine
  | cons first rest =>
      cases rest with
      | nil =>
          simp [AxisDirection.polylineLastDirection,
            AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine, AxisDirection.opposite] at genuine
      | cons second tail => simp

private theorem unitSubdividePolyline_length_ge_two_of_length_ge_two
    {route : List Cell}
    (length : 2 ≤ route.length)
    (orthogonal : OrthogonalPolyline route) :
    2 ≤ (AxisDirection.unitSubdividePolyline route).length := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second tail =>
          exact AxisDirection.unitSubdividePolyline_length_ge_two
            (first := first) (second := second) (rest := tail) orthogonal

/-- A route-order certificate transfers when the three terminal directions
agree for every atom that actually has three tagged occurrences. -/
private theorem variableRoutesInOccurrenceOrder_of_threeDirections
    {Variable : Type*} [DecidableEq Variable]
    {formula : PositionedPeriodicCNF Variable}
    {rawRoutes normalizedRoutes : PositionedPeriodicCNF.IncidenceRoutes}
    (rawOrdered :
      formula.VariableRoutesInOccurrenceOrder rawRoutes)
    (directions :
      ∀ atom first second third,
        PeriodicOneInThreeToThreeDM.occurrenceAt
            formula.erase atom .first = some first →
        PeriodicOneInThreeToThreeDM.occurrenceAt
            formula.erase atom .second = some second →
        PeriodicOneInThreeToThreeDM.occurrenceAt
            formula.erase atom .third = some third →
        AxisDirection.polylineLastDirection
              (normalizedRoutes first.2.1 first.2.2) =
            AxisDirection.polylineLastDirection
              (rawRoutes first.2.1 first.2.2) ∧
          AxisDirection.polylineLastDirection
              (normalizedRoutes second.2.1 second.2.2) =
            AxisDirection.polylineLastDirection
              (rawRoutes second.2.1 second.2.2) ∧
          AxisDirection.polylineLastDirection
              (normalizedRoutes third.2.1 third.2.2) =
            AxisDirection.polylineLastDirection
              (rawRoutes third.2.1 third.2.2)) :
    formula.VariableRoutesInOccurrenceOrder normalizedRoutes := by
  intro atom first second third
    firstLookup secondLookup thirdLookup
  rcases directions atom first second third
      firstLookup secondLookup thirdLookup with
    ⟨firstDirection, secondDirection, thirdDirection⟩
  rw [firstDirection, secondDirection, thirdDirection]
  exact rawOrdered atom first second third
    firstLookup secondLookup thirdLookup

/-- Final loop erasure preserves the terminal direction of one concrete
twice-inherited incidence. -/
theorem
    retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_lastDirection_of_inherited
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
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (literalSource : literal.atom = .inl (.inl sourceAtom)) :
    AxisDirection.polylineLastDirection
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  let rawRoute :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex
  have rawOrthogonal : OrthogonalPolyline rawRoute := by
    simpa only [rawRoute] using
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2
  rcases
      retainedOrderedFixedEightComposedRawIncidenceRoutes_lastDirection_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        sourceAtom literalSource with
    ⟨data, _dataLookup, rawDirection⟩
  have clearanceLength :
      2 ≤
        (retainedFigureNineClearanceIncidenceRoutes
          source data.sourceClauseIndex data.sourceLiteralIndex).length := by
    have lengthThree :=
      retainedFigureNineClearanceIncidenceRoutes_length_ge_three
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        data.sourceLiteralMember
    omega
  have clearanceDirectionGenuine :
      (AxisDirection.polylineLastDirection
        (retainedFigureNineClearanceIncidenceRoutes
          source data.sourceClauseIndex
          data.sourceLiteralIndex)).IsGenuine :=
    AxisDirection.polylineLastDirection_isGenuine clearanceLength
      (retainedFigureNineClearanceIncidenceRoutes_unitSteps
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        data.sourceLiteralMember)
  have rawLength : 2 ≤ rawRoute.length := by
    apply two_le_length_of_polylineLastDirection_isGenuine
    rw [show AxisDirection.polylineLastDirection rawRoute =
        AxisDirection.polylineLastDirection
          (retainedFigureNineClearanceIncidenceRoutes
            source data.sourceClauseIndex data.sourceLiteralIndex) by
      simpa only [rawRoute] using rawDirection]
    exact clearanceDirectionGenuine
  have rawFresh :
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline rawRoute) := by
    simpa only [rawRoute] using
      retainedOrderedFixedEightComposedRawIncidenceRoutes_lastNotInDropLast_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        sourceAtom literalSource
  simpa only [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes, rawRoute] using
    AxisDirection.polylineLastDirection_normalizeOrthogonalPolyline_of_lastNotInDropLast
      (unitSubdividePolyline_length_ge_two_of_length_ge_two
        rawLength rawOrthogonal)
      rawOrthogonal rawFresh

/-- A tagged final occurrence of a twice-inherited atom retains its raw
terminal direction after normalization. -/
private theorem
    retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_slotDirection
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (finalEq :
      DecidableEq
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (sourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (tagged :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (lookup :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable))
          finalEq
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).erase
          (.inl (.inl sourceAtom)) slot = some tagged) :
    AxisDirection.polylineLastDirection
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty tagged.2.1 tagged.2.2) =
      AxisDirection.polylineLastDirection
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty tagged.2.1 tagged.2.2) := by
  have info :=
    @PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      finalEq
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).erase
      (.inl (.inl sourceAtom)) slot tagged lookup
  rcases PositionedPeriodicCNF.exists_positionedOccurrence_of_tagged
      _ info.1 with
    ⟨clause, clauseMember, literalMember⟩
  exact
    retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_lastDirection_of_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      sourceAtom info.2

/-- The final normalized ordered Figure 9 route family retains clockwise
variable occurrence order. -/
theorem
    retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
      (inferInstance)
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  have rawOrderedNested :
      @PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))
        PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
    apply
      @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))
        _ PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
    exact
      retainedOrderedFixedEightComposedRawIncidenceRoutes_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  apply variableRoutesInOccurrenceOrder_of_threeDirections
    (rawOrdered := rawOrderedNested)
  intro outputAtom first second third
    firstLookup secondLookup thirdLookup
  have thirdSemantic :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable))
          PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula
              (retainedFigureNineClearancePositionedFormula source).erase))
          outputAtom .third = some third := by
    simpa only [
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
      PeriodicOneInThreeNoUnitsPositioned.erase_formula,
      PeriodicOneInThreePositioned.erase_formula] using thirdLookup
  rcases
      PlanarOneInThreeNoUnitsFigureNine.exists_sourceAtom_of_occurrenceAt_third
        (retainedFigureNineClearancePositionedFormula source).erase
        PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
        outputAtom third thirdSemantic with
    ⟨sourceAtom, outputAtomEq⟩
  subst outputAtom
  have firstDirection :=
    retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_slotDirection
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
      sourceAtom .first first firstLookup
  have secondDirection :=
    retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_slotDirection
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
      sourceAtom .second second secondLookup
  have thirdDirection :=
    retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_slotDirection
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
      sourceAtom .third third thirdLookup
  exact ⟨firstDirection, secondDirection, thirdDirection⟩

end PeriodicOrthocrossing
end LeanTrominoes
