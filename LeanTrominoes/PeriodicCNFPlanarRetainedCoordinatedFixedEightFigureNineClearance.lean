import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightClauseDirectionOrdering
import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparationScaling
import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparationOrdering
import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackCompleteSeparation

/-!
# Whole-source clearance before Figure 9

The composed Figure 9 connector fan extends a bounded distance around each
source clause.  We therefore refine the already completed clockwise source
drawing once more before inserting those fixed-size connectors.  Scaling
does not change the logical periodic CNF; normalization after scaling restores
unit steps while retaining the enlarged geometric clearance.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- Extra whole-source refinement reserved for the fixed composed Figure 9
connector fans. -/
def retainedFigureNineSourceClearanceFactor : Nat := 2

@[simp]
theorem retainedFigureNineSourceClearanceFactor_eq :
    retainedFigureNineSourceClearanceFactor = 2 := by
  rfl

theorem retainedFigureNineSourceClearanceFactor_pos :
    0 < retainedFigureNineSourceClearanceFactor := by
  native_decide

/-- The clockwise source presentation after the extra whole-source
refinement. -/
def retainedFigureNineClearancePositionedFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
    source).scale retainedFigureNineSourceClearanceFactor

/-- Variable placement paired with the whole-source Figure 9 refinement. -/
def retainedFigureNineClearancePlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source).scale
    retainedFigureNineSourceClearanceFactor

/-- Scale the complete clockwise source routes, then restore their unit-grid
presentation by verified orthogonal normalization. -/
def retainedFigureNineClearanceIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes
    (PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedFigureNineSourceClearanceFactor
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source))

/-- The extra coordinate refinement leaves the source width unchanged. -/
theorem retainedFigureNineClearancePositionedFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3) :
    (retainedFigureNineClearancePositionedFormula
      source).erase.WidthAtMost 3 := by
  simpa [retainedFigureNineClearancePositionedFormula] using
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_widthAtMostThree
      source sourceWidth

/-- The extra Figure Nine clearance scale preserves the absence of empty
ordered retained source clauses. -/
theorem retainedFigureNineClearancePositionedFormula_clausesNonempty
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ clause ∈
        (retainedFigureNineClearancePositionedFormula source).clauses,
      clause.literals ≠ [] := by
  intro clause clauseMember
  rw [retainedFigureNineClearancePositionedFormula,
    PositionedPeriodicCNF.scale_clauses] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨unscaledClause, unscaledClauseMember, rfl⟩
  simpa using
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_clausesNonempty
      source sourceClausesNonempty unscaledClause unscaledClauseMember

/-- The extra coordinate refinement leaves per-clause atom distinctness
unchanged. -/
theorem retainedFigureNineClearancePositionedFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedFigureNineClearancePositionedFormula source).AllAtomsNodup := by
  apply PositionedPeriodicCNF.AllAtomsNodup.scale
  exact
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty

/-- Membership in the scaled clearance presentation recovers the precise
unscaled clockwise clause at the same list index. -/
theorem exists_clockwiseClause_of_clearanceClause_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx) :
    ∃ sourceClause,
      (sourceClause, clauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx ∧
      clause = sourceClause.scale retainedFigureNineSourceClearanceFactor := by
  rw [retainedFigureNineClearancePositionedFormula,
    PositionedPeriodicCNF.scale_clauses, List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  have indexEqual : taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have clauseEqual :
      taggedClause.1.scale retainedFigureNineSourceClearanceFactor = clause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  exact ⟨taggedClause.1, taggedClauseMember, clauseEqual.symm⟩

/-- Every genuine clearance route has its scaled canonical endpoints and is
orthogonal. -/
theorem retainedFigureNineClearanceIncidenceRoutes_valid
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
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedFigureNineClearanceIncidenceRoutes
      source clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedFigureNineClearancePlacement source) clause) ∧
      (retainedFigureNineClearanceIncidenceRoutes
        source clauseIndex literalIndex).getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (retainedFigureNineClearancePlacement source)
              clause literal) ∧
      OrthogonalPolyline
        (retainedFigureNineClearanceIncidenceRoutes
          source clauseIndex literalIndex) := by
  rcases exists_clockwiseClause_of_clearanceClause_mem clauseMember with
    ⟨sourceClause, sourceClauseMember, clauseEq⟩
  subst clause
  have sourceLiteralMember :
      (literal, literalIndex) ∈ sourceClause.literals.zipIdx := by
    simpa using literalMember
  let sourceRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source clauseIndex literalIndex
  let scaledRoute :=
    scalePolyline retainedFigureNineSourceClearanceFactor sourceRoute
  have sourceValid :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty sourceClauseMember sourceLiteralMember
  have sourceNonempty : sourceRoute ≠ [] := by
    intro empty
    simp [sourceRoute, empty] at sourceValid
  have scaledNonempty : scaledRoute ≠ [] := by
    simpa [scaledRoute, scalePolyline] using sourceNonempty
  have scaledOrthogonal : OrthogonalPolyline scaledRoute :=
    sourceValid.2.2.scalePolyline
      retainedFigureNineSourceClearanceFactor_pos
  have normalizedHead :=
    AxisDirection.normalizeOrthogonalPolyline_head?
      scaledNonempty scaledOrthogonal
  have normalizedLast :=
    AxisDirection.normalizeOrthogonalPolyline_getLast?
      scaledNonempty scaledOrthogonal
  have normalizedOrthogonal :=
    AxisDirection.normalizeOrthogonalPolyline_orthogonal
      scaledNonempty scaledOrthogonal
  change
    (AxisDirection.normalizeOrthogonalPolyline scaledRoute).head? = _ ∧
      (AxisDirection.normalizeOrthogonalPolyline scaledRoute).getLast? = _ ∧
      OrthogonalPolyline
        (AxisDirection.normalizeOrthogonalPolyline scaledRoute)
  refine ⟨normalizedHead.trans ?_, normalizedLast.trans ?_,
    normalizedOrthogonal⟩
  · simp [scaledRoute, sourceRoute,
      retainedFigureNineClearancePlacement, sourceValid.1]
  · simp [scaledRoute, sourceRoute,
      retainedFigureNineClearancePlacement, sourceValid.2.1,
      PositionedPeriodicCNF.canonicalLiteralPosition,
      Cell.scale_add]

/-- The unnormalized scaled route behind every genuine clearance incidence
is nonempty, orthogonal, simple, and contains at least one edge. -/
private theorem retainedFigureNineClearanceScaledRoute_data
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
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let scaledRoute :=
      scalePolyline retainedFigureNineSourceClearanceFactor
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
          source clauseIndex literalIndex)
    scaledRoute ≠ [] ∧
      OrthogonalPolyline scaledRoute ∧
      LocalIncidenceDrawing.RouteIsSimple scaledRoute ∧
      2 ≤ scaledRoute.length := by
  rcases exists_clockwiseClause_of_clearanceClause_mem clauseMember with
    ⟨sourceClause, sourceClauseMember, clauseEq⟩
  subst clause
  have sourceLiteralMember :
      (literal, literalIndex) ∈ sourceClause.literals.zipIdx := by
    simpa using literalMember
  let sourceRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source clauseIndex literalIndex
  let scaledRoute :=
    scalePolyline retainedFigureNineSourceClearanceFactor sourceRoute
  have sourceValid :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty sourceClauseMember sourceLiteralMember
  have sourceNonempty : sourceRoute ≠ [] := by
    intro empty
    simp [sourceRoute, empty] at sourceValid
  have factorPositiveInt :
      0 < (retainedFigureNineSourceClearanceFactor : Int) := by
    exact_mod_cast retainedFigureNineSourceClearanceFactor_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [scaledRoute, scalePolyline] using sourceNonempty
  · exact sourceValid.2.2.scalePolyline
      retainedFigureNineSourceClearanceFactor_pos
  · exact routeIsSimple_scalePolyline factorPositiveInt
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_isSimple
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember)
  · simpa [scaledRoute, sourceRoute, scalePolyline] using
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember)

/-- On every genuine incidence, the clearance route is exactly the ordered
unit subdivision of the factor-two scaled clockwise source route.  This
exposes the route shape used when the Figure 9 connector is spliced to its
first two refined source steps. -/
theorem retainedFigureNineClearanceIncidenceRoutes_eq_unitSubdividePolyline
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
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    retainedFigureNineClearanceIncidenceRoutes
        source clauseIndex literalIndex =
      AxisDirection.unitSubdividePolyline
        (scalePolyline retainedFigureNineSourceClearanceFactor
          (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
            source clauseIndex literalIndex)) := by
  have scaledData :=
    retainedFigureNineClearanceScaledRoute_data
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  simpa [retainedFigureNineClearanceIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes,
    PositionedPeriodicCNF.scaleIncidenceRoutes] using
      AxisDirection.normalizeOrthogonalPolyline_eq_unitSubdividePolyline_of_simple
        scaledData.1 scaledData.2.1 scaledData.2.2.1

/-- Every genuine normalized clearance route is a geometrically simple
path. -/
theorem retainedFigureNineClearanceIncidenceRoutes_isSimple
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
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (retainedFigureNineClearanceIncidenceRoutes
        source clauseIndex literalIndex) := by
  have scaledData :=
    retainedFigureNineClearanceScaledRoute_data
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  simpa [retainedFigureNineClearanceIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes,
    PositionedPeriodicCNF.scaleIncidenceRoutes] using
      AxisDirection.normalizeOrthogonalPolyline_isSimple
        scaledData.1 scaledData.2.1

/-- Every genuine normalized clearance route consists of unit lattice
steps. -/
theorem retainedFigureNineClearanceIncidenceRoutes_unitSteps
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
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedFigureNineClearanceIncidenceRoutes
      source clauseIndex literalIndex).IsChain
        AxisDirection.IsUnitAxisStep := by
  have scaledData :=
    retainedFigureNineClearanceScaledRoute_data
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  simpa [retainedFigureNineClearanceIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes,
    PositionedPeriodicCNF.scaleIncidenceRoutes] using
      AxisDirection.normalizeOrthogonalPolyline_unitSteps
        scaledData.1 scaledData.2.1

/-- Normalization of the simple scaled source route preserves a real first
edge. -/
theorem retainedFigureNineClearanceIncidenceRoutes_length_ge_two
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
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedFigureNineClearanceIncidenceRoutes
        source clauseIndex literalIndex).length := by
  have scaledData :=
    retainedFigureNineClearanceScaledRoute_data
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  rw [retainedFigureNineClearanceIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes,
    PositionedPeriodicCNF.scaleIncidenceRoutes,
    AxisDirection.normalizeOrthogonalPolyline_eq_unitSubdividePolyline_of_simple
      scaledData.1 scaledData.2.1 scaledData.2.2.1]
  exact AxisDirection.unitSubdividePolyline_length_ge_two_of_length_ge_two
    scaledData.2.2.2 scaledData.2.1

/-- Every genuine normalized clearance route exposes its first exit vertex. -/
theorem retainedFigureNineClearanceIncidenceRoutes_exits
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
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ exit,
      (retainedFigureNineClearanceIncidenceRoutes
        source clauseIndex literalIndex).tail.head? = some exit := by
  have routeLength :=
    retainedFigureNineClearanceIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  cases routeEq : retainedFigureNineClearanceIncidenceRoutes
      source clauseIndex literalIndex with
  | nil => simp [routeEq] at routeLength
  | cons first rest =>
      cases rest with
      | nil => simp [routeEq] at routeLength
      | cons exit suffix => exact ⟨exit, rfl⟩

/-- Scaling and simple orthogonal normalization preserve the clockwise
source route's first direction exactly. -/
theorem retainedFigureNineClearanceIncidenceRoutes_firstDirection
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
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (retainedFigureNineClearanceIncidenceRoutes
          source clauseIndex literalIndex) =
      AxisDirection.polylineFirstDirection
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
          source clauseIndex literalIndex) := by
  have scaledData :=
    retainedFigureNineClearanceScaledRoute_data
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  let sourceRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source clauseIndex literalIndex
  let scaledRoute :=
    scalePolyline retainedFigureNineSourceClearanceFactor sourceRoute
  change
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline scaledRoute) =
      AxisDirection.polylineFirstDirection sourceRoute
  calc
    _ = AxisDirection.polylineFirstDirection scaledRoute :=
      AxisDirection.polylineFirstDirection_normalizeOrthogonalPolyline_of_simple
        scaledData.2.2.2 scaledData.2.1 scaledData.2.2.1
    _ = AxisDirection.polylineFirstDirection sourceRoute := by
      exact AxisDirection.polylineFirstDirection_scalePolyline
        retainedFigureNineSourceClearanceFactor
        (by exact_mod_cast retainedFigureNineSourceClearanceFactor_pos)
        sourceRoute

/-- Every clearance route has a genuine first cardinal direction. -/
theorem retainedFigureNineClearanceIncidenceRoutes_directionsGenuine
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.ClauseRouteDirectionsGenuine
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearanceIncidenceRoutes source) := by
  intro clause clauseIndex clauseMember literal literalIndex literalMember
  exact AxisDirection.polylineFirstDirection_isGenuine
    (retainedFigureNineClearanceIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember)
    (retainedFigureNineClearanceIncidenceRoutes_unitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember)

/-- The extra clearance refinement preserves the strict clockwise rank order
of the displayed clause exits. -/
theorem retainedFigureNineClearanceIncidenceRoutes_ranksStrictlyIncrease
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.ClauseRouteDirectionRanksStrictlyIncrease
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearanceIncidenceRoutes source) := by
  intro clause clauseIndex clauseMember first second firstLtSecond
  rcases exists_clockwiseClause_of_clearanceClause_mem clauseMember with
    ⟨sourceClause, sourceClauseMember, clauseEq⟩
  subst clause
  have firstSourceLt : first.val < sourceClause.literals.length := by
    exact first.isLt
  have secondSourceLt : second.val < sourceClause.literals.length := by
    exact second.isLt
  let firstLiteral := sourceClause.literals[first.val]'firstSourceLt
  let secondLiteral := sourceClause.literals[second.val]'secondSourceLt
  have firstSourceMember :
      (firstLiteral, first.val) ∈ sourceClause.literals.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨firstSourceLt, rfl⟩
  have secondSourceMember :
      (secondLiteral, second.val) ∈ sourceClause.literals.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨secondSourceLt, rfl⟩
  have firstScaledMember :
      (firstLiteral, first.val) ∈
        (sourceClause.scale
          retainedFigureNineSourceClearanceFactor).literals.zipIdx := by
    simpa using firstSourceMember
  have secondScaledMember :
      (secondLiteral, second.val) ∈
        (sourceClause.scale
          retainedFigureNineSourceClearanceFactor).literals.zipIdx := by
    simpa using secondSourceMember
  have firstDirection :=
    retainedFigureNineClearanceIncidenceRoutes_firstDirection
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember firstScaledMember
  have secondDirection :=
    retainedFigureNineClearanceIncidenceRoutes_firstDirection
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember secondScaledMember
  rw [firstDirection, secondDirection]
  exact
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_ranksStrictlyIncrease
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty sourceClause clauseIndex sourceClauseMember
      ⟨first.val, firstSourceLt⟩ ⟨second.val, secondSourceLt⟩
      firstLtSecond

/-- Every nonempty clearance clause still selects one of the verified finite
Figure 9 connector fans. -/
theorem retainedFigureNineClearance_clauseExitFanData_valid
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
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    (clauseNonempty : clause.literals ≠ []) :
    (PositionedPeriodicCNF.clauseExitFanData
      clause clauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)).IsValid := by
  apply PositionedPeriodicCNF.clauseExitFanData_valid
    (retainedFigureNineClearanceIncidenceRoutes_directionsGenuine
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedFigureNineClearanceIncidenceRoutes_ranksStrictlyIncrease
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    clauseMember
  · exact List.length_pos_iff.mpr clauseNonempty
  · rcases exists_clockwiseClause_of_clearanceClause_mem clauseMember with
      ⟨sourceClause, sourceClauseMember, clauseEq⟩
    subst clause
    simpa using
      PositionedPeriodicCNF.orderClausesByRouteDirection_clause_length_le
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        3
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)
        sourceClauseMember

/-- The clearance refinement changes no logical satisfiability information. -/
theorem retainedFigureNineClearancePositionedFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3) :
    (retainedFigureNineClearancePositionedFormula
      source).erase.Satisfiable ↔ source.Satisfiable := by
  simpa [retainedFigureNineClearancePositionedFormula] using
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_satisfiable_iff
      source sourceLocal sourceWidth sourceOccurrences

/-- The clearance placement still has a positive physical period. -/
theorem retainedFigureNineClearancePlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    0 < (retainedFigureNineClearancePlacement source).period := by
  rw [retainedFigureNineClearancePlacement,
    PeriodicVariablePlacement.scale_period]
  exact Nat.mul_pos retainedFigureNineSourceClearanceFactor_pos
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_pos
      source)

/-- Clockwise clause reindexing preserves the complete relative separation
certificate of the normalized retained source drawing. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source) := by
  apply
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther.orderCanonicalRoutesByClauseDirection
  exact
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther_of_copiedSource
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      (retainedFinalCopiedSourceRoutes_relativeAvoidEachOther
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- Relative route separation survives the extra whole-source refinement and
the following simple orthogonal normalization. -/
theorem retainedFigureNineClearanceIncidenceRoutes_relativeAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearanceIncidenceRoutes source) := by
  have scaledSeparated :
      PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedFigureNineSourceClearanceFactor
          (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
            source)) := by
    simpa [retainedFigureNineClearancePositionedFormula,
      retainedFigureNineClearancePlacement] using
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).scale
          retainedFigureNineSourceClearanceFactor_pos
  have normalizedSeparated :=
    scaledSeparated.normalizeOrthogonalIncidenceRoutes
      (fun incidence incidenceMember => by
        rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
            (retainedFigureNineClearancePositionedFormula source)
            incidenceMember with
          ⟨clause, literal, clauseMember, literalMember,
            _incidenceEqual⟩
        have scaledData :=
          retainedFigureNineClearanceScaledRoute_data
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember
        simpa [PositionedPeriodicCNF.scaleIncidenceRoutes] using scaledData.1)
      (fun incidence incidenceMember => by
        rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
            (retainedFigureNineClearancePositionedFormula source)
            incidenceMember with
          ⟨clause, literal, clauseMember, literalMember,
            _incidenceEqual⟩
        have scaledData :=
          retainedFigureNineClearanceScaledRoute_data
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember
        simpa [PositionedPeriodicCNF.scaleIncidenceRoutes] using
          scaledData.2.1)
  simpa [retainedFigureNineClearanceIncidenceRoutes] using
    normalizedSeparated

end PeriodicOrthocrossing
end LeanTrominoes
