import LeanTrominoes.RetainedAngularFanFinalCycleSeparation

/-!
# Periodic separation of the final Figure 7 cycles

The fixed-eight cycle-separation theorem initially compares only the stored
fundamental representatives.  This file extends its macrocell argument to a
second route in an arbitrary nonzero period cell.  The gauged retained source
places every source atom strictly inside one fundamental square, so distinct
period cells have distinct factor-36 cycle macrocells.  Their routes are
therefore strictly contact-free, even when they are copies of the same stored
incidence.
-/

namespace LeanTrominoes

namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Uniform scaling commutes with translating every point of a polyline. -/
theorem scalePolyline_translatePolyline
    (factor : Int) (offset : Cell) (route : List Cell) :
    scalePolyline factor (translatePolyline offset route) =
      translatePolyline (Cell.scale factor offset)
        (scalePolyline factor route) := by
  unfold scalePolyline translatePolyline
  simp only [List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  exact cell_scale_add factor offset point

end PeriodicOrthocrossing

namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- If two source positions are distinct after one semantic period shift,
then the corresponding positioned Figure 7 routes are strictly separated.
The second route is translated by the induced period of the factor-36 split
placement. -/
theorem positionedCycleRoutes_strictlyAvoid_of_relative_positions_ne
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {firstAtom secondAtom : Variable}
    (relativeTranslate : Cell)
    (positionsDifferent :
      sourcePlacement.position firstAtom ≠
        Cell.add (sourcePlacement.position secondAtom)
          (sourcePlacement.translation relativeTranslate))
    (firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat) :
    RoutesStrictlyAvoidEachOther
      (positionedCycleRoutes sourcePlacement firstAtom
        firstClauseIndex firstLiteralIndex)
      (translatePolyline
        ((placement sourcePlacement).translation relativeTranslate)
        (positionedCycleRoutes sourcePlacement secondAtom
          secondClauseIndex secondLiteralIndex)) := by
  let shift :=
    (placement sourcePlacement).translation relativeTranslate
  apply routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower := positionedCycleRouteLower sourcePlacement firstAtom)
      (firstUpper := positionedCycleRouteUpper sourcePlacement firstAtom)
      (secondLower :=
        Cell.add shift
          (positionedCycleRouteLower sourcePlacement secondAtom))
      (secondUpper :=
        Cell.add shift
          (positionedCycleRouteUpper sourcePlacement secondAtom))
  · intro point pointMember
    exact positionedCycleRoutes_inClosedGridRectangle
      sourcePlacement firstAtom
      firstClauseIndex firstLiteralIndex pointMember
  · intro point pointMember
    unfold translatePolyline at pointMember
    rcases List.mem_map.mp pointMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    have bounded :=
      positionedCycleRoutes_inClosedGridRectangle
        sourcePlacement secondAtom
        secondClauseIndex secondLiteralIndex sourcePointMember
    rcases physicalShiftEq :
        (placement sourcePlacement).translation relativeTranslate with
      ⟨shiftX, shiftY⟩
    rcases lowerEq :
        positionedCycleRouteLower sourcePlacement secondAtom with
      ⟨lowerX, lowerY⟩
    rcases upperEq :
        positionedCycleRouteUpper sourcePlacement secondAtom with
      ⟨upperX, upperY⟩
    rcases sourcePoint with ⟨pointX, pointY⟩
    simpa only [shift, physicalShiftEq,
      InClosedGridRectangle, Cell.add] using
      (show
        shiftX + lowerX ≤ shiftX + pointX ∧
          shiftX + pointX ≤ shiftX + upperX ∧
          shiftY + lowerY ≤ shiftY + pointY ∧
          shiftY + pointY ≤ shiftY + upperY by
        simp only [InClosedGridRectangle, lowerEq, upperEq] at bounded
        omega)
  · rcases firstPositionEq : sourcePlacement.position firstAtom with
      ⟨firstX, firstY⟩
    rcases secondPositionEq : sourcePlacement.position secondAtom with
      ⟨secondX, secondY⟩
    rcases relativeTranslate with ⟨translateX, translateY⟩
    have coordinateDifferent :
        firstX ≠
            secondX + sourcePlacement.period * translateX ∨
          firstY ≠
            secondY + sourcePlacement.period * translateY := by
      by_contra coordinatesNotDifferent
      simp only [not_or, not_not] at coordinatesNotDifferent
      apply positionsDifferent
      rw [firstPositionEq, secondPositionEq]
      simp only [PeriodicVariablePlacement.translation,
        Cell.add, Cell.scale, Prod.mk.injEq]
      exact coordinatesNotDifferent
    have shiftEq :
        shift =
          Cell.scale refinementScale
            (sourcePlacement.translation
              (translateX, translateY)) := by
      rcases sourcePlacement with ⟨period, position⟩
      simp [shift, placement,
        PeriodicVariablePlacement.translation,
        refinementScale, Cell.scale]
      constructor <;> ring
    simp only [ClosedGridRectanglesSeparated,
      positionedCycleRouteLower, positionedCycleRouteUpper,
      macroOrigin, shiftEq,
      PeriodicVariablePlacement.translation,
      refinementScale, firstPositionEq, secondPositionEq,
      Cell.add, Cell.sub, Cell.scale]
    rcases coordinateDifferent with
        horizontalDifferent | verticalDifferent <;> omega

/-- All flattened Figure 7 routes in a nonzero relative period cell are
strictly separated from all routes in the fundamental representative,
provided the source placement has no such translated position collision. -/
theorem allCycleRoutes_strictlyAvoidEachOther_of_relative_positions_ne
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (relativePositionsDifferent :
      ∀ {firstAtom secondAtom : Variable},
        firstAtom ∈ PeriodicThreeSATThree.sourceVariables source.erase →
        secondAtom ∈ PeriodicThreeSATThree.sourceVariables source.erase →
        ∀ relativeTranslate,
          relativeTranslate ≠ (0, 0) →
          sourcePlacement.position firstAtom ≠
            Cell.add (sourcePlacement.position secondAtom)
              (sourcePlacement.translation relativeTranslate))
    {firstClause secondClause :
      PositionedPeriodicClause (ThreeOccurrenceVariable Variable)}
    {firstCycleIndex secondCycleIndex : Nat}
    (firstClauseMember :
      (firstClause, firstCycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    (secondClauseMember :
      (secondClause, secondCycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (ThreeOccurrenceVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (_firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (_secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (allCycleRoutes source sourcePlacement
        firstCycleIndex firstLiteralIndex)
      (translatePolyline
        ((placement sourcePlacement).translation relativeTranslate)
        (allCycleRoutes source sourcePlacement
          secondCycleIndex secondLiteralIndex)) := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement firstClauseMember with
    ⟨firstMetadata, firstMetadataLookup,
      _firstClauseEqual, _firstLocalClauseMember⟩
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement secondClauseMember with
    ⟨secondMetadata, secondMetadataLookup,
      _secondClauseEqual, _secondLocalClauseMember⟩
  have firstAtomMember :=
    allCycleClauseMetadata_lookup_atom_mem
      source sourcePlacement firstMetadataLookup
  have secondAtomMember :=
    allCycleClauseMetadata_lookup_atom_mem
      source sourcePlacement secondMetadataLookup
  have strict :=
    positionedCycleRoutes_strictlyAvoid_of_relative_positions_ne
      sourcePlacement relativeTranslate
      (relativePositionsDifferent firstAtomMember secondAtomMember
        relativeTranslate relativeTranslateNonzero)
      firstMetadata.localClauseIndex firstLiteralIndex
      secondMetadata.localClauseIndex secondLiteralIndex
  change
    RoutesStrictlyAvoidEachOther
      (match
        (allCycleClauseMetadata source sourcePlacement)[firstCycleIndex]?
       with
       | none => []
       | some metadata =>
          positionedCycleRoutes sourcePlacement metadata.atom
            metadata.localClauseIndex firstLiteralIndex)
      (translatePolyline
        ((placement sourcePlacement).translation relativeTranslate)
        (match
          (allCycleClauseMetadata source sourcePlacement)[secondCycleIndex]?
         with
         | none => []
         | some metadata =>
            positionedCycleRoutes sourcePlacement metadata.atom
              metadata.localClauseIndex secondLiteralIndex))
  rw [firstMetadataLookup, secondMetadataLookup]
  exact strict

end PeriodicEightOccurrenceSplitPositioned

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Two points strictly inside one placement's fundamental square cannot
coincide after a nonzero semantic period translation. -/
theorem PeriodicVariablePlacement.position_ne_add_translation_of_inSquare_of_nonzero
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (periodPositive : 0 < placement.period)
    {first second : Cell}
    (firstBounds :
      0 < first.1 ∧ first.1 < placement.period ∧
        0 < first.2 ∧ first.2 < placement.period)
    (secondBounds :
      0 < second.1 ∧ second.1 < placement.period ∧
        0 < second.2 ∧ second.2 < placement.period)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    first ≠
      Cell.add second (placement.translation relativeTranslate) := by
  intro positionsEqual
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases relativeTranslate with ⟨translateX, translateY⟩
  have periodPositiveInt : (0 : Int) < placement.period := by
    exact_mod_cast periodPositive
  simp only [PeriodicVariablePlacement.translation,
    Cell.add, Cell.scale, Prod.mk.injEq] at positionsEqual
  have coordinateShiftZero
      {firstCoordinate secondCoordinate shift : Int}
      (firstLower : 0 < firstCoordinate)
      (firstUpper : firstCoordinate < placement.period)
      (secondLower : 0 < secondCoordinate)
      (secondUpper : secondCoordinate < placement.period)
      (coordinateEq :
        firstCoordinate =
          secondCoordinate + placement.period * shift) :
      shift = 0 := by
    by_contra shiftNonzero
    have shiftCases : shift ≤ -1 ∨ 1 ≤ shift := by omega
    rcases shiftCases with shiftNegative | shiftPositive
    · have productBound :=
        mul_le_mul_of_nonneg_left shiftNegative
          (le_of_lt periodPositiveInt)
      norm_num at productBound
      omega
    · have productBound :=
        mul_le_mul_of_nonneg_left shiftPositive
          (le_of_lt periodPositiveInt)
      norm_num at productBound
      omega
  have translateXZero : translateX = 0 :=
    coordinateShiftZero
      firstBounds.1 firstBounds.2.1
      secondBounds.1 secondBounds.2.1
      positionsEqual.1
  have translateYZero : translateY = 0 :=
    coordinateShiftZero
      firstBounds.2.2.1 firstBounds.2.2.2
      secondBounds.2.2.1 secondBounds.2.2.2
      positionsEqual.2
  exact relativeTranslateNonzero
    (Prod.ext translateXZero translateYZero)

/-- Two gauged retained source positions cannot coincide after a nonzero
semantic period shift, even after the source-clearance scaling. -/
theorem
    retainedFinalCoordinatedScaledPlacement_position_ne_add_translation_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (firstAtom secondAtom : WrappedPeriodicPlanarSATVariable Variable)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    placement.position firstAtom ≠
      Cell.add (placement.position secondAtom)
        (placement.translation relativeTranslate) := by
  let basePlacement := finalCoordinatedPlacement formula
  let placement :=
    basePlacement.scale retainedAngularFanSourceClearanceFactor
  have firstBaseBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula firstAtom
  have secondBaseBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula secondAtom
  have firstBounds :
      0 < (placement.position firstAtom).1 ∧
        (placement.position firstAtom).1 < placement.period ∧
        0 < (placement.position firstAtom).2 ∧
        (placement.position firstAtom).2 < placement.period := by
    rcases firstPositionEq : basePlacement.position firstAtom with
      ⟨firstX, firstY⟩
    simpa [placement, basePlacement, finalCoordinatedPlacement,
      firstPositionEq, retainedAngularFanSourceClearanceFactor,
      Cell.scale] using firstBaseBounds
  have secondBounds :
      0 < (placement.position secondAtom).1 ∧
        (placement.position secondAtom).1 < placement.period ∧
        0 < (placement.position secondAtom).2 ∧
        (placement.position secondAtom).2 < placement.period := by
    rcases secondPositionEq : basePlacement.position secondAtom with
      ⟨secondX, secondY⟩
    simpa [placement, basePlacement, finalCoordinatedPlacement,
      secondPositionEq, retainedAngularFanSourceClearanceFactor,
      Cell.scale] using secondBaseBounds
  have basePeriodPositive : 0 < basePlacement.period := by
    simpa [basePlacement, finalCoordinatedPlacement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  have periodPositive : 0 < placement.period := by
    exact Nat.mul_pos
      (by simp [retainedAngularFanSourceClearanceFactor])
      basePeriodPositive
  exact
    PeriodicVariablePlacement.position_ne_add_translation_of_inSquare_of_nonzero
      placement periodPositive firstBounds secondBounds
      relativeTranslate relativeTranslateNonzero

/-- The actual factor-eight Figure 7 cycle routes are strictly separated
from every nonzero translated period copy. -/
theorem
    retainedFinalSourceScaledAllCycleRoutes_strictlyAvoidEachOther_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstCycleIndex secondCycleIndex : Nat}
    (firstClauseMember :
      (firstClause, firstCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    (secondClauseMember :
      (secondClause, secondCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          firstCycleIndex firstLiteralIndex))
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            secondCycleIndex secondLiteralIndex))) := by
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  have unscaledStrict :=
    allCycleRoutes_strictlyAvoidEachOther_of_relative_positions_ne
      source placement
      (fun {firstAtom secondAtom} _firstAtomMember _secondAtomMember
          translate translateNonzero =>
        retainedFinalCoordinatedScaledPlacement_position_ne_add_translation_of_nonzero
          formula firstAtom secondAtom translate translateNonzero)
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      relativeTranslate relativeTranslateNonzero
  have scaledStrict :=
    unscaledStrict.scalePolyline
      (show (0 : Int) < retainedTerminalFanRoutingRefinement by
        simp [retainedTerminalFanRoutingRefinement])
  rw [scalePolyline_translatePolyline] at scaledStrict
  simpa [source, placement,
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
    retainedAngularFanSourceScaledRefinedPlacement,
    retainedAngularFanRefinedPlacement,
    finalCoordinatedPlacement] using scaledStrict

/-- Public appended-cycle routes inherit strict separation from every
nonzero translated period copy. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_cycleRoutes_strictlyAvoidEachOther_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstCycleIndex secondCycleIndex : Nat}
    (firstClauseMember :
      (firstClause, firstCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    (secondClauseMember :
      (secondClause, secondCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let occurrencePorts :=
      occurrencePortsOfAngularOrder source.erase
        (angularOccurrenceOrder source.erase routes)
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula
        ((occurrenceClauses source occurrencePorts).length +
          firstCycleIndex)
        firstLiteralIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula
          ((occurrenceClauses source occurrencePorts).length +
            secondCycleIndex)
          secondLiteralIndex)) := by
  dsimp only
  rw [
    retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
      formula firstCycleIndex firstLiteralIndex,
    retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
      formula secondCycleIndex secondLiteralIndex]
  exact
    retainedFinalSourceScaledAllCycleRoutes_strictlyAvoidEachOther_of_nonzero
      formula firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      relativeTranslate relativeTranslateNonzero

end PeriodicOrthocrossing
end LeanTrominoes
