import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineIndex
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineSelector
import LeanTrominoes.PeriodicOneInThreePositionedLocalRoutes

/-!
# Metadata-selected local composed routes

The composed metadata index selects one certified Figure 9-plus-unit-
elimination drawing and its exact local clause number for every clause of
the actual two-stage positioned formula.

This file packages those selected physical routes and proves exact endpoints
and orthogonality for every genuine incidence.  Incidences inherited from
the original source still end at the composed neighborhood's boundary port;
the later splicing layer will attach the external source-route tail there.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- Route family obtained by selecting the certified composed drawing
recorded at each final flattened clause index. -/
def localRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match (formulaClauseMetadata source)[clauseIndex]? with
    | none => []
    | some metadata =>
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).routes
            metadata.localClauseIndex literalIndex

/-- A genuine final clause selects exactly the composed drawing and local
clause index retained by its metadata. -/
theorem localRoutes_of_clause_member
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (literalIndex : Nat) :
    ∃ metadata : ClauseMetadata Variable,
      metadata.clause = clause ∧
      localRoutes source clauseIndex literalIndex =
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).routes
            metadata.localClauseIndex literalIndex := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  refine ⟨metadata, clauseEqual, ?_⟩
  simp [localRoutes, metadataLookup]

/-- Every genuine selected route meets its displayed final clause and the
exact variable endpoint advertised by its composed finite drawing. -/
theorem localRoutes_endpoints_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ metadata : ClauseMetadata Variable,
      (formulaClauseMetadata source)[clauseIndex]? =
          some metadata ∧
        metadata.clause = clause ∧
        (localRoutes source clauseIndex literalIndex).head? =
          some clause.position ∧
        (localRoutes source clauseIndex literalIndex).getLast? =
          some
            ((instantiatedDrawing
              metadata.sourceClauseIndex
              metadata.figureNineClauseStart
              metadata.sourceClause).variablePosition literal.atom) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid_embedded
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  have metadataDistinct :
      metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause metadataSourceMember
  let drawing :=
    instantiatedDrawing
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        composedClauseGadget
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause :=
    instantiatedDrawing_formula
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause,
        metadata.localClauseIndex) ∈
        drawing.formula.zipIdx := by
    rw [drawingFormula]
    exact localClauseMember
  have embeddedLiteralMember :
      ((literal.atom, literal.value), literalIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, literalIndex),
        metadataLiteralMember, rfl⟩
  have drawingValid :
      drawing.IsValid :=
    instantiatedDrawing_isValid
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
  have localEndpoints :=
    EmbeddedCNFIncidenceDrawing.physicalRoutesMatch
      drawing drawingValid.1
      (PlanarOneInThreeNoUnits.embedPositionedClause
        metadata.clause)
      metadata.localClauseIndex embeddedClauseMember
      (literal.atom, literal.value)
      literalIndex embeddedLiteralMember
  refine
    ⟨metadata, metadataLookup, clauseEqual, ?_, ?_⟩
  · simpa [localRoutes, metadataLookup, drawing,
      PlanarOneInThreeNoUnits.embedPositionedClause,
      clauseEqual]
      using localEndpoints.1
  · simpa [localRoutes, metadataLookup, drawing]
      using localEndpoints.2

/-- Every genuine selected composed route is orthogonal. -/
theorem localRoutes_orthogonal_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (localRoutes source clauseIndex literalIndex) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid_embedded
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  have metadataDistinct :
      metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause metadataSourceMember
  let drawing :=
    instantiatedDrawing
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        composedClauseGadget
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause :=
    instantiatedDrawing_formula
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause,
        metadata.localClauseIndex) ∈
        drawing.formula.zipIdx := by
    rw [drawingFormula]
    exact localClauseMember
  have embeddedLiteralMember :
      ((literal.atom, literal.value), literalIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, literalIndex),
        metadataLiteralMember, rfl⟩
  have drawingValid :
      drawing.IsValid :=
    instantiatedDrawing_isValid
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
  have selectedOrthogonal :=
    PeriodicOneInThreePositioned.embeddedRoute_orthogonal_of_members
      drawing drawingValid.2.1
      embeddedClauseMember embeddedLiteralMember
  simpa [localRoutes, metadataLookup, drawing] using
    selectedOrthogonal

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
