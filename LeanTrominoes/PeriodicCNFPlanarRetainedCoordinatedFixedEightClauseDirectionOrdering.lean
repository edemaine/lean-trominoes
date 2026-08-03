import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeRoutes
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteSeparation

/-!
# Clockwise clause exits for the retained fixed-eight drawing

The normalized retained source drawing is continuously separated, so the
routes incident to one clause leave its canonical clause point in distinct
cardinal directions.  Reordering each clause by those directions therefore
puts every ternary clause in the clockwise order expected by the three fixed
Figure 9 boundary ports.

The reordering retains the original route indices and changes only their
whole-period anchor gauges.  This file also records the logical invariants
needed by the eventual hardness reduction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- The source-scaled retained formula with each clause's literals ordered
by the clockwise rank of its normalized source-route exits. -/
def
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PositionedPeriodicCNF.orderClausesByRouteDirection
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source)

/-- Reindexed normalized routes, translated by whole periods into the
canonical anchor gauge of the reordered source clause. -/
def
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source)

/-- Reordering preserves the source's width-three bound. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3) :
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
      source).erase.WidthAtMost 3 := by
  exact
    (PositionedPeriodicCNF.orderClausesByRouteDirection_widthAtMost_iff
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      3).mpr
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)

/-- Reordering preserves collision-free atoms within every clause. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
      source).AllAtomsNodup := by
  exact
    (PositionedPeriodicCNF.orderClausesByRouteDirection_allAtomsNodup_iff
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)).mpr
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)

/-- Clause-direction ordering changes no satisfiability information. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3) :
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
      source).erase.Satisfiable ↔ source.Satisfiable := by
  calc
    _ ↔
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).erase.Satisfiable :=
      PositionedPeriodicCNF.orderClausesByRouteDirection_satisfiable_iff
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
    _ ↔ (retainedDrawingEightOccurrenceSplitFormula source).Satisfiable := by
      rw [
        retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase]
    _ ↔ source.Satisfiable :=
      retainedDrawingEightOccurrenceSplitFormula_satisfiable_iff
        source sourceLocal sourceWidth sourceOccurrences

/-- Every ternary clause in the reordered retained drawing has its three
normalized routes in clockwise order. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_ternaryClockwise
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.TernaryClauseRoutesInClockwiseOrder
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source) := by
  apply
    PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection_ternaryClockwise
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact AxisDirection.polylineFirstDirection_isGenuine
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_length_ge_two
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_unitSteps
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)
  · intro clause clauseIndex clauseMember
      first firstIndex firstMember
      second secondIndex secondMember indexNe
    have firstValid :=
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember firstMember
    have secondValid :=
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember secondMember
    apply polylineFirstDirections_ne_of_routesAvoidEachOther
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_length_ge_two
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember firstMember)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_length_ge_two
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember secondMember)
      firstValid.2.2 secondValid.2.2
    · rw [firstValid.1, secondValid.1]
    · exact
        retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_avoidEachOther
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          clauseMember clauseMember firstMember secondMember
          (Or.inr indexNe)

end PeriodicOrthocrossing
end LeanTrominoes
