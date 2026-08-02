import LeanTrominoes.PeriodicCNFPlanarRetainedFixedEightOneInThreePositioned
import LeanTrominoes.PeriodicOneInThreePositionedInheritedRouteFamily
import LeanTrominoes.RetainedAngularFanFinalNormalizedVariableRouteOrder

/-!
# Figure 9 routes over the coordinated retained fixed-eight source

The final coordinated fixed-eight route family lives over the source-scaled
positioned formula.  This file feeds that formula, placement, and route
certificate directly into the generic positioned Figure 9 adapter.  It is
the first downstream layer to use the coordinated routes rather than the
older unscaled angular-spliced family.

Coordinate scaling changes no literals, so the source formula has the same
width and collision-free fixed-eight atom distinctness as the established
presentation.  The resulting raw exact-one routes have canonical endpoints,
are orthogonal, and expose the first exit needed by unit elimination.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- The source-scaled coordinated fixed-eight formula still has width at
most three. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source).erase.WidthAtMost 3 := by
  rw [
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase]
  exact
    retainedDrawingEightOccurrenceSplitFormula_widthAtMostThree
      sourceWidth

/-- Scaling the fixed-eight geometry preserves its collision-free
per-clause atom distinctness. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source).AllAtomsNodup := by
  unfold
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
    retainedAngularFanSourceScaledRefinedFormula
    retainedAngularFanRefinedFormula
  apply PositionedPeriodicCNF.AllAtomsNodup.scale
  apply PeriodicEightOccurrenceSplitPositioned.formula_allAtomsNodup
  rw [PositionedPeriodicCNF.erase_scale,
    angularOccurrenceOrder_scaleIncidenceRoutes
      _ retainedAngularFanSourceClearanceFactor_pos]
  exact
    retainedDrawingAngularOccurrencePorts_collisionFree
      sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty

/-- Direct positioned Figure 9 image of the source-scaled coordinated
fixed-eight split. -/
def
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThreePositioned.formula
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source)

/-- Placement of the raw Figure 9 variables over the source-scaled
coordinated fixed-eight split. -/
def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThreePositioned.placement
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)

@[simp]
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
      source).erase =
      PeriodicOneInThree.formula
        (retainedDrawingEightOccurrenceSplitFormula source) := by
  simp [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula]

/-- Figure 9 suffixes inherited from the normalized coordinated fixed-eight
routes. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement
        source)
      (PeriodicOneInThreePositioned.normalizedLocalEndpoint
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source)) :=
  PeriodicOneInThreePositioned.inheritedRouteSuffixes
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

/-- Complete local-plus-inherited raw Figure 9 routes over the coordinated
fixed-eight family. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicOneInThreePositioned.splicedRoutes
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Every genuine coordinated raw Figure 9 route has its canonical
endpoints and is orthogonal. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement
              source)
            clause) ∧
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement
              source)
            clause literal) ∧
      OrthogonalPolyline
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  simpa [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement] using
    PeriodicOneInThreePositioned.splicedRoutes_valid_of_members
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember

/-- Every genuine coordinated raw Figure 9 route has a first exit after
its generated clause endpoint. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_exists_tail_head?
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ exit,
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).tail.head? =
          some exit := by
  simpa [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement] using
    PeriodicOneInThreePositioned.splicedRoutes_exists_tail_head?_of_members
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
