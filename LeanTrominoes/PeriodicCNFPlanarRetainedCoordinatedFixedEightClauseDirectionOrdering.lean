import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeRoutes
import LeanTrominoes.PositionedPeriodicCNFClauseExitFanOrdering
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

/-- Every genuine reordered retained route has the canonical endpoints of
the reordered clause presentation and remains orthogonal. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              source)
            clause) ∧
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source clauseIndex literalIndex).getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                source)
              clause literal) ∧
      OrthogonalPolyline
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
          source clauseIndex literalIndex) := by
  simpa only [
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula,
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes]
    using
      PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection_valid_of
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
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
            sourceClausesNonempty sourceClauseMember sourceLiteralMember).2.2)
        clauseMember literalMember

/-- Reindexing by clockwise clause direction and changing the whole-period
anchor gauge preserve the absence of repeated route points. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source clauseIndex literalIndex).Nodup := by
  rcases PositionedPeriodicCNF.exists_sourceLiteral_of_orderedLiteral_mem
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      clauseMember literalMember with
    ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
      sourceClauseMember, sourceLiteralMember,
      clauseEq, literalEq, orderedRouteEq⟩
  have sourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp sourceClauseMember
  subst clause
  subst literal
  rw [retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes,
    PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection,
    sourceClauseLookup, orderedRouteEq]
  unfold translatePolyline
  apply List.Nodup.map (Cell.add_left_injective _)
  exact
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_isSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty sourceClauseMember sourceLiteralMember).1

/-- Clockwise reindexing and anchor-gauge translation preserve the complete
geometric simplicity certificate of every source route. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_isSimple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source clauseIndex literalIndex) := by
  rcases PositionedPeriodicCNF.exists_sourceLiteral_of_orderedLiteral_mem
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      clauseMember literalMember with
    ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
      sourceClauseMember, sourceLiteralMember,
      clauseEq, literalEq, orderedRouteEq⟩
  have sourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp sourceClauseMember
  subst clause
  subst literal
  rw [retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes,
    PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection,
    sourceClauseLookup, orderedRouteEq]
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_isSimple
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember)
      _

/-- Every reordered retained source route still consists of unit lattice
steps. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_unitSteps
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source clauseIndex literalIndex).IsChain
        AxisDirection.IsUnitAxisStep := by
  exact
    PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection_unitSteps
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      (fun sourceClause sourceClauseIndex sourceClauseMember
          sourceLiteral sourceLiteralIndex sourceLiteralMember =>
        retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_unitSteps
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember)
      clauseMember literalMember

/-- Every reordered retained source route contains at least one edge. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source clauseIndex literalIndex).length := by
  exact
    PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection_length_ge
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      2
      (fun sourceClause sourceClauseIndex sourceClauseMember
          sourceLiteral sourceLiteralIndex sourceLiteralMember =>
        retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_length_ge_two
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember)
      clauseMember literalMember

/-- Every genuine reordered route exposes a first exit vertex after its
canonical clause endpoint. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_exits
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ exit,
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source clauseIndex literalIndex).tail.head? = some exit := by
  have routeLength :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  cases routeEq :
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source clauseIndex literalIndex with
  | nil => simp [routeEq] at routeLength
  | cons first rest =>
      cases rest with
      | nil => simp [routeEq] at routeLength
      | cons exit suffix =>
          exact ⟨exit, rfl⟩

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

/-- Every normalized retained source route has a genuine first direction. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_directionsGenuine
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.ClauseRouteDirectionsGenuine
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source) := by
  intro clause clauseIndex clauseMember literal literalIndex literalMember
  exact AxisDirection.polylineFirstDirection_isGenuine
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_unitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember)

/-- Distinct incidences at one retained source clause leave it in distinct
first directions. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_directionsPairwiseDistinct
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx →
      ∀ first firstIndex,
        (first, firstIndex) ∈ clause.literals.zipIdx →
        ∀ second secondIndex,
          (second, secondIndex) ∈ clause.literals.zipIdx →
          firstIndex ≠ secondIndex →
          AxisDirection.polylineFirstDirection
              (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
                source clauseIndex firstIndex) ≠
            AxisDirection.polylineFirstDirection
              (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
                source clauseIndex secondIndex) := by
  intro clause clauseIndex clauseMember
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

/-- Every reordered retained source route still has a genuine first
direction. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_directionsGenuine
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.ClauseRouteDirectionsGenuine
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source) :=
  PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection_directionsGenuine
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_directionsGenuine
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- In every reordered clause, source-route first-direction ranks strictly
increase with literal index. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_ranksStrictlyIncrease
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.ClauseRouteDirectionRanksStrictlyIncrease
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source) :=
  PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection_ranksStrictlyIncrease
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_directionsGenuine
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_directionsPairwiseDistinct
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

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
  · exact
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_directionsGenuine
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · exact
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_directionsPairwiseDistinct
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty

/-- Every nonempty reordered retained clause selects a valid finite
port-to-exit connector fan. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplit_clauseExitFanData_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    (clauseNonempty : clause.literals ≠ []) :
    (PositionedPeriodicCNF.clauseExitFanData
      clause clauseIndex
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source)).IsValid := by
  apply PositionedPeriodicCNF.clauseExitFanData_valid
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_directionsGenuine
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_ranksStrictlyIncrease
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    clauseMember
  · exact List.length_pos_iff.mpr clauseNonempty
  · exact
      PositionedPeriodicCNF.orderClausesByRouteDirection_clause_length_le
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        3
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)
        clauseMember

end PeriodicOrthocrossing
end LeanTrominoes
