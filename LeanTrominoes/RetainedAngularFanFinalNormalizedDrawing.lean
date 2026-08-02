import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteSeparation
import LeanTrominoes.PeriodicGridDrawingLoopErasure

/-!
# The assembled normalized final periodic drawing

This file installs the normalized final incidence routes in the standard
positioned periodic drawing.  Canonical endpoints give exact graph-route
matching, the normalizer gives unit steps and orthogonality, and unit steps
make the integer-grid planarity predicate automatic.  Exact continuous
separation between translated occurrences remains a separate obligation.
-/

namespace LeanTrominoes

namespace PositionedPeriodicCNF

/-- Pointwise unit-step certificates for genuine incidences lift to the
assembled periodic incidence drawing. -/
theorem incidenceDrawing_hasUnitSteps_of_pointwise
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (unitSteps :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          (routes clauseIndex literalIndex).IsChain
            AxisDirection.IsUnitAxisStep) :
    (incidenceDrawing source placement routes).HasUnitSteps := by
  intro route routeMember
  change route ∈ incidenceEdgeRoutes source routes at routeMember
  rw [incidenceEdgeRoutes_eq_metadata_map] at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨incidence, incidenceMember, routeEqual⟩
  subst route
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨incidenceIndexLt, incidenceAt⟩
  rcases incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, literal, clauseMember, literalMember, _⟩
  exact unitSteps _ _ clauseMember _ _ literalMember

end PositionedPeriodicCNF

namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- The unnormalized coordinated drawing underlying the normalized final
drawing. -/
def retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      formula)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula)
    (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula)

/-- The final positioned fixed-eight drawing with every incidence route
unit-subdivided and loop-erased. -/
def retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      formula)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      formula)

/-- The final normalized drawing is exactly drawing-level loop erasure of
the coordinated source drawing. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_eq_normalize
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing
        formula =
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceDrawing
        formula).normalizeOrthogonalRoutes := by
  have routesEqual :
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula =
        PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes
          (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
            formula) := by
    funext clauseIndex literalIndex
    rfl
  rw [retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing,
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceDrawing,
    routesEqual]
  exact PositionedPeriodicCNF.incidenceDrawing_normalizeOrthogonalRoutes
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula)

/-- The normalized drawing routes realize every edge of the final periodic
incidence graph with its exact translated endpoints. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing
      formula).RoutesMatch
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).erase.incidenceGraph := by
  simpa only [
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing,
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitCanonicalOrthogonalRoutes] using
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitCanonicalOrthogonalRoutes
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).routesMatch
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_pos
          formula)

/-- Every stored route in the normalized drawing consists of genuine unit
axis steps. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_hasUnitSteps
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing
      formula).HasUnitSteps := by
  rw [retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing]
  apply PositionedPeriodicCNF.incidenceDrawing_hasUnitSteps_of_pointwise
  intro clause clauseIndex clauseMember literal literalIndex literalMember
  exact
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_unitSteps
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

/-- The assembled normalized final drawing is orthogonal. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing
      formula).IsOrthogonal := by
  simpa only [
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing,
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitCanonicalOrthogonalRoutes] using
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitCanonicalOrthogonalRoutes
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).isOrthogonal

/-- Unit steps make the normalized final drawing planar for the established
integer-grid predicate. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing
      formula).IsPlanar :=
  PeriodicGridDrawing.isPlanar_of_hasUnitSteps
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_hasUnitSteps
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes
