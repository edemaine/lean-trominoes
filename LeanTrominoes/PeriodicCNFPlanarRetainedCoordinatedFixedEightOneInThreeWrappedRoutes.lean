import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeInheritedRouteIsolation
import LeanTrominoes.PositionedPeriodicCNFCanonicalRouteRenaming

/-!
# Coordinated Figure 9 routes through opaque wrapping

Opaque wrapping changes no coordinates, offsets, or presentation indices.
The raw coordinated Figure 9 routes can therefore be reused verbatim.
Generic route-renaming lemmas transport their canonical endpoints,
orthogonality, and first-exit certificate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- Opaque positioned exact-one output over the coordinated fixed-eight
geometry. -/
def
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
    source).rename WrappedPeriodicVariable.mk

/-- Placement transported through the opaque exact-one wrapper. -/
def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) where
  period :=
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement
      source).period
  position := fun wrapped =>
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement
      source).position wrapped.original

@[simp]
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source).erase =
      wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (retainedDrawingEightOccurrenceSplitFormula source)) := by
  rw [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    PositionedPeriodicCNF.erase_rename,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_erase]
  rfl

/-- Figure 9 itself introduces no repeated atom within a coordinated raw
clause. -/
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
      source).AllAtomsNodup := by
  exact
    PeriodicOneInThreePositioned.formula_allAtomsNodup
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)

/-- Opaque wrapping preserves coordinated Figure 9 atom distinctness. -/
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source).AllAtomsNodup := by
  apply PositionedPeriodicCNF.allAtomsNodup_rename
    WrappedPeriodicVariable.mk
  · intro first second equal
    exact WrappedPeriodicVariable.mk.inj equal
  · exact
      retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_allAtomsNodup
        source

/-- The wrapped coordinated Figure 9 source has width at most three. -/
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source).erase.WidthAtMost 3 := by
  rw [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_erase]
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact PeriodicOneInThree.formula_widthAtMostThree _

/-- The raw coordinated Figure 9 route family, reused after opaque
wrapping. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
    source sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty

/-- Every wrapped coordinated Figure 9 route keeps its canonical endpoints
and orthogonality. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement
              source)
            clause) ∧
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement
              source)
            clause literal) ∧
      OrthogonalPolyline
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  let rawFormula :=
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
      source
  let rawPlacement :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement source
  let wrappedPlacement :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source
  let routes :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have rawEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ rawFormula.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (routes sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  rawPlacement sourceClause) ∧
            (routes sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  rawPlacement sourceClause sourceLiteral) := by
    intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    have valid :=
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember
    exact ⟨valid.1, valid.2.1⟩
  have rawOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ rawFormula.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          OrthogonalPolyline
            (routes sourceClauseIndex sourceLiteralIndex) := by
    intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    exact
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember).2.2
  have endpoints :=
    PositionedPeriodicCNF.canonicalIncidenceRoutes_endpoints_rename
      rawFormula rawPlacement wrappedPlacement routes
      WrappedPeriodicVariable.mk rawEndpoints
      (fun _ => rfl) rfl clauseMember literalMember
  have orthogonal :=
    PositionedPeriodicCNF.canonicalIncidenceRoutes_orthogonal_rename
      rawFormula routes WrappedPeriodicVariable.mk rawOrthogonal
      clauseMember literalMember
  simpa [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes,
    rawFormula, rawPlacement, wrappedPlacement, routes,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement] using
      ⟨endpoints.1, endpoints.2, orthogonal⟩

/-- Opaque wrapping preserves both endpoint-isolation certificates of every
coordinated Figure 9 route. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_endpointIsolation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline
          (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseIndex literalIndex)) ∧
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline
          (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseIndex literalIndex)) := by
  let rawFormula :=
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
      source
  let routes :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have transferred :=
    PositionedPeriodicCNF.incidenceIndexProperty_rename
      rawFormula WrappedPeriodicVariable.mk
      (fun sourceClauseIndex sourceLiteralIndex =>
        AxisDirection.HeadNotInTail
            (AxisDirection.unitSubdividePolyline
              (routes sourceClauseIndex sourceLiteralIndex)) ∧
          AxisDirection.LastNotInDropLast
            (AxisDirection.unitSubdividePolyline
              (routes sourceClauseIndex sourceLiteralIndex)))
      (fun _sourceClause _sourceClauseIndex sourceClauseMember
          _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
        retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_endpointIsolation
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember)
      clauseMember literalMember
  simpa [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    rawFormula, routes] using transferred

/-- Opaque wrapping also preserves every coordinated Figure 9 route's first
exit. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_exists_tail_head?
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ exit,
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).tail.head? =
          some exit := by
  let rawFormula :=
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
      source
  let routes :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have transferred :=
    PositionedPeriodicCNF.incidenceIndexProperty_rename
      rawFormula WrappedPeriodicVariable.mk
      (fun sourceClauseIndex sourceLiteralIndex =>
        ∃ exit,
          (routes sourceClauseIndex sourceLiteralIndex).tail.head? =
            some exit)
      (fun _sourceClause _sourceClauseIndex sourceClauseMember
          _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
        retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_exists_tail_head?
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember)
      clauseMember literalMember
  simpa
    [retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes,
      retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
      rawFormula, routes] using transferred

end PeriodicOrthocrossing
end LeanTrominoes
