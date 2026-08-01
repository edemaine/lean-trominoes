import LeanTrominoes.RetainedAngularFanFinalDirectSourceSameOriginOtherTargetSeparation

/-!
# Complete cross-clause separation for final direct-source routes

The local direct atlas occupies only the lower `14 × 14` route rectangle
inside each `20 × 20` planar-SAT macrocell.  Consequently the radius-288
route envelopes at the final refinement remain disjoint whenever their
physical macrocell origins differ.

Together with the shared-target and shared-origin certificates, this closes
all three cases for complete Figure 7 routes selected by different final
source clauses.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

private instance decidableForallFintype
    {α : Type*} [Fintype α]
    (predicate : α → Prop)
    [∀ value, Decidable (predicate value)] :
    Decidable (∀ value, predicate value) :=
  Fintype.decidableForallFintype

/-- Both endpoints of every local direct route lie in the occupied
`[0,13] × [0,13]` part of its planar-SAT macrocell. -/
theorem retainedDirectSourceLocalRouteAt_endpoints_in_routeMacrocell :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      let route := retainedDirectSourceLocalRouteAt kind index
      (0 ≤ (route.head?.getD (0, 0)).1 ∧
          (route.head?.getD (0, 0)).1 ≤ 13 ∧
          0 ≤ (route.head?.getD (0, 0)).2 ∧
          (route.head?.getD (0, 0)).2 ≤ 13) ∧
        (0 ≤ (route.getLast?.getD (0, 0)).1 ∧
          (route.getLast?.getD (0, 0)).1 ≤ 13 ∧
          0 ≤ (route.getLast?.getD (0, 0)).2 ∧
          (route.getLast?.getD (0, 0)).2 ≤ 13) := by
  native_decide

/-- Direct route envelopes based at different planar-SAT macrocell centers
are separated after the final common refinement. -/
theorem
    RetainedDirectSourceRouteChoice.sourceRectanglesSeparated_of_originCenters_ne
    (first second : RetainedDirectSourceRouteChoice)
    (firstCenter secondCenter : Cell)
    (firstOrigin :
      first.origin = Cell.scale planarMacroScale firstCenter)
    (secondOrigin :
      second.origin = Cell.scale planarMacroScale secondCenter)
    (centersDifferent : firstCenter ≠ secondCenter) :
    first.SourceRectanglesSeparated second := by
  rcases first with ⟨firstOriginCell, firstKind, firstIndex⟩
  rcases second with ⟨secondOriginCell, secondKind, secondIndex⟩
  rcases firstCenter with ⟨firstCenterX, firstCenterY⟩
  rcases secondCenter with ⟨secondCenterX, secondCenterY⟩
  have centerCoordinatesDifferent :
      firstCenterX ≠ secondCenterX ∨
        firstCenterY ≠ secondCenterY := by
    by_cases differentX : firstCenterX ≠ secondCenterX
    · exact Or.inl differentX
    · exact Or.inr fun equalY =>
        centersDifferent
          (Prod.ext (not_ne_iff.mp differentX) equalY)
  rcases
      (retainedDirectSourceLocalRouteAt
        firstKind firstIndex).head?.getD (0, 0) with
    ⟨firstHeadX, firstHeadY⟩
  rcases
      (retainedDirectSourceLocalRouteAt
        firstKind firstIndex).getLast?.getD (0, 0) with
    ⟨firstLastX, firstLastY⟩
  rcases
      (retainedDirectSourceLocalRouteAt
        secondKind secondIndex).head?.getD (0, 0) with
    ⟨secondHeadX, secondHeadY⟩
  rcases
      (retainedDirectSourceLocalRouteAt
        secondKind secondIndex).getLast?.getD (0, 0) with
    ⟨secondLastX, secondLastY⟩
  have firstBounds :=
    retainedDirectSourceLocalRouteAt_endpoints_in_routeMacrocell
      firstKind firstIndex
  have secondBounds :=
    retainedDirectSourceLocalRouteAt_endpoints_in_routeMacrocell
      secondKind secondIndex
  simp only at firstOrigin secondOrigin
  simp only [Cell.scale, planarMacroScale] at firstOrigin secondOrigin
  rcases firstOriginCell with ⟨firstOriginX, firstOriginY⟩
  rcases secondOriginCell with ⟨secondOriginX, secondOriginY⟩
  simp only [Prod.mk.injEq] at firstOrigin secondOrigin
  simp only at firstBounds secondBounds
  unfold RetainedDirectSourceRouteChoice.SourceRectanglesSeparated
  simp only [RetainedDirectSourceRouteChoice.sourceSegment,
    GridSegment.coordinateLower, GridSegment.coordinateUpper,
    coordinateRadiusLower, coordinateRadiusUpper,
    Cell.add, Cell.scale,
    retainedTerminalFanTotalRefinement_eq,
    ClosedGridRectanglesSeparated]
  norm_num
  rcases centerCoordinatesDifferent with differentX | differentY
  · rcases lt_or_gt_of_ne differentX with less | greater
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
  · rcases lt_or_gt_of_ne differentY with less | greater
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Successful final direct choices with distinct physical component
origins have strictly separated complete Figure 7 routes. -/
theorem
    retainedFinalDirectSourceDifferentOrigin_completeFigure7Routes_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
    (firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat)
    (firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some firstChoice)
    (secondChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex =
        some secondChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (originsDifferent :
      firstChoice.origin ≠ secondChoice.origin) :
    RoutesStrictlyAvoidEachOther
      (firstChoice.completeFigure7Route firstSlot)
      (secondChoice.completeFigure7Route secondSlot) := by
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula firstClauseIndex firstLiteralIndex
      firstChoice firstChoiceLookup with
    ⟨firstData⟩
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula secondClauseIndex secondLiteralIndex
      secondChoice secondChoiceLookup with
    ⟨secondData⟩
  have centersDifferent :
      firstData.center ≠ secondData.center := by
    intro centersEqual
    apply originsDifferent
    rw [firstData.originEq, secondData.originEq, centersEqual]
  exact
    firstChoice.completeFigure7Routes_strictlyAvoid_of_sourceRectanglesSeparated
      secondChoice firstSlot secondSlot
      (firstChoice.sourceRectanglesSeparated_of_originCenters_ne
        secondChoice
        firstData.center secondData.center
        firstData.originEq secondData.originEq centersDifferent)

/-- Complete Figure 7 routes chosen by different final source clauses are
strictly separated in all target and component-origin configurations. -/
theorem
    retainedFinalDirectSourceCrossClause_completeFigure7Routes_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some firstChoice)
    (secondChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex =
        some secondChoice)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula secondLiteral secondClauseIndex secondLiteralIndex
    RoutesStrictlyAvoidEachOther
      (firstChoice.completeFigure7Route firstSlot)
      (secondChoice.completeFigure7Route secondSlot) := by
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  by_cases targetsEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral
  · exact
      retainedFinalDirectSourceCrossClauseSameTarget_completeFigure7Routes_strictlyAvoid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstChoice secondChoice
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceLookup secondChoiceLookup
        clauseIndicesDifferent targetsEqual
  · by_cases originsEqual :
        firstChoice.origin = secondChoice.origin
    · exact
        retainedFinalDirectSourceCrossClauseSameOriginOtherTarget_completeFigure7Routes_strictlyAvoid
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstChoice secondChoice
          firstClauseMember secondClauseMember
          firstLiteralMember secondLiteralMember
          firstChoiceLookup secondChoiceLookup
          clauseIndicesDifferent targetsEqual originsEqual
    · exact
        retainedFinalDirectSourceDifferentOrigin_completeFigure7Routes_strictlyAvoid
          formula firstChoice secondChoice
          firstClauseIndex firstLiteralIndex
          secondClauseIndex secondLiteralIndex
          firstChoiceLookup secondChoiceLookup
          firstSlot secondSlot originsEqual

end PeriodicEightOccurrenceSplit
end LeanTrominoes
