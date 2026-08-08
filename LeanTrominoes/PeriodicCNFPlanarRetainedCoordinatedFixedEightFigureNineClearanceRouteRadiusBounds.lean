import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteRadiusBounds
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance

/-!
# Variable-centered radius bounds through Figure 9 source clearance

Orthogonal loop erasure preserves coordinate-radius bounds, clockwise clause
ordering preserves the rebased routes exactly up to their canonical anchor
translation, and uniform Figure 9 source refinement scales both the radius
and the placement period.  This module applies those generic transports to
the retained fixed-eight pipeline through the final pre-Figure-9 clearance
presentation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 4000000

/-- Loop erasure and unit subdivision preserve the coordinated one-period
variable-radius certificate. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source) := by
  have bounds :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_withinVariablePeriod
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have normalized :=
    bounds.normalizeOrthogonalIncidenceRoutes
      (by
        intro clause clauseIndex clauseMember
          literal literalIndex literalMember
        have valid :=
          retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember
        intro routeEmpty
        rw [routeEmpty] at valid
        simp at valid)
      (by
        intro clause clauseIndex clauseMember
          literal literalIndex literalMember
        exact
          (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember).2.2)
  change
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
      (PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          source))
  exact normalized

/-- Clockwise clause-direction ordering preserves the normalized one-period
variable-radius certificate. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        source)
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source) := by
  have ordered :=
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_withinVariablePeriod
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
      |>.orderCanonicalRoutesByClauseDirection
  simpa [
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula,
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes]
    using ordered

/-- The factor-two source refinement and subsequent loop erasure preserve a
one-period variable-radius certificate for the complete Figure 9 clearance
route family. -/
theorem retainedFigureNineClearanceIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearanceIncidenceRoutes source) := by
  let sourceFormula :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
      source
  let sourcePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  let sourceRoutes :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source
  have sourceBounds :
      PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
        sourceFormula sourcePlacement sourceRoutes := by
    simpa [sourceFormula, sourcePlacement, sourceRoutes] using
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_withinVariablePeriod
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  have scaledBounds :=
    sourceBounds.scale retainedFigureNineSourceClearanceFactor
  have normalizedBounds :=
    scaledBounds.normalizeOrthogonalIncidenceRoutes
      (by
        intro scaledClause clauseIndex scaledClauseMember
          literal literalIndex literalMember
        rw [PositionedPeriodicCNF.scale_clauses,
          List.zipIdx_map] at scaledClauseMember
        rcases List.mem_map.mp scaledClauseMember with
          ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
        have clauseIndexEqual :
            taggedClause.2 = clauseIndex :=
          congrArg Prod.snd taggedClauseEqual
        have scaledClauseEqual :
            taggedClause.1.scale retainedFigureNineSourceClearanceFactor =
              scaledClause :=
          congrArg Prod.fst taggedClauseEqual
        subst clauseIndex
        subst scaledClause
        have sourceLiteralMember :
            (literal, literalIndex) ∈
              taggedClause.1.literals.zipIdx := by
          simpa using literalMember
        have sourceValid :=
          retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty taggedClauseMember sourceLiteralMember
        intro scaledEmpty
        have sourceNonempty :
            sourceRoutes taggedClause.2 literalIndex ≠ [] := by
          intro sourceEmpty
          have sourceHead := sourceValid.1
          change
            (sourceRoutes taggedClause.2 literalIndex).head? = _
            at sourceHead
          rw [sourceEmpty] at sourceHead
          simp at sourceHead
        apply sourceNonempty
        simpa [PositionedPeriodicCNF.scaleIncidenceRoutes,
          scalePolyline] using scaledEmpty)
      (by
        intro scaledClause clauseIndex scaledClauseMember
          literal literalIndex literalMember
        rw [PositionedPeriodicCNF.scale_clauses,
          List.zipIdx_map] at scaledClauseMember
        rcases List.mem_map.mp scaledClauseMember with
          ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
        have clauseIndexEqual :
            taggedClause.2 = clauseIndex :=
          congrArg Prod.snd taggedClauseEqual
        have scaledClauseEqual :
            taggedClause.1.scale retainedFigureNineSourceClearanceFactor =
              scaledClause :=
          congrArg Prod.fst taggedClauseEqual
        subst clauseIndex
        subst scaledClause
        have sourceLiteralMember :
            (literal, literalIndex) ∈
              taggedClause.1.literals.zipIdx := by
          simpa using literalMember
        have sourceOrthogonal :=
          (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty taggedClauseMember sourceLiteralMember).2.2
        simpa [PositionedPeriodicCNF.scaleIncidenceRoutes,
          sourceRoutes] using
          sourceOrthogonal.scalePolyline
            retainedFigureNineSourceClearanceFactor_pos)
  simpa [retainedFigureNineClearancePositionedFormula,
    retainedFigureNineClearancePlacement,
    retainedFigureNineClearanceIncidenceRoutes,
    sourceFormula, sourcePlacement, sourceRoutes]
    using normalizedBounds

end PeriodicOrthocrossing
end LeanTrominoes
