import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedIndex
import LeanTrominoes.PlanarOneInThreeNoUnitsSelector
import LeanTrominoes.PeriodicOneInThreePositionedLocalRoutes
import LeanTrominoes.EmbeddedCNFIncidenceDrawingPlanarity

/-!
# Metadata-selected local unit-elimination routes

The unit-elimination metadata index selects the certified local drawing and
local clause number for every flattened output clause.  This file packages
the resulting route family and proves every genuine selected route
orthogonal.  As at the Figure 9 layer, inherited source-variable incidences
will receive their outer prefixes in the subsequent splicing layer.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

open PlanarThreeSAT

/-- Route family obtained by selecting the certified local unit-elimination
drawing recorded at each flattened output-clause index. -/
def localRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match (formulaClauseMetadata source)[clauseIndex]? with
    | none => []
    | some metadata =>
        (PlanarOneInThreeNoUnits.instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.sourceClause).routes
            metadata.localClauseIndex literalIndex

/-- A genuine output clause selects exactly the local drawing and local
clause index retained by its metadata. -/
theorem localRoutes_of_clause_member
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    (literalIndex : Nat) :
    ∃ metadata : ClauseMetadata Variable,
      metadata.clause = clause ∧
      localRoutes source clauseIndex literalIndex =
        (PlanarOneInThreeNoUnits.instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.sourceClause).routes
            metadata.localClauseIndex literalIndex := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  refine ⟨metadata, clauseEqual, ?_⟩
  simp [localRoutes, metadataLookup]

/-- Every genuine local unit-elimination route is orthogonal when the source
has width at most three and distinct atoms in every clause. -/
theorem localRoutes_orthogonal_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (localRoutes source clauseIndex literalIndex) := by
  rcases formulaClauseMetadata_lookup_valid
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
    PlanarOneInThreeNoUnits.instantiatedDrawing
      metadata.sourceClauseIndex metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        (clauseGadget metadata.sourceClauseIndex
          metadata.sourceClause).map
            PlanarOneInThreeNoUnits.embedPositionedClause :=
    PlanarOneInThreeNoUnits.instantiatedDrawing_formula
      metadata.sourceClauseIndex metadata.sourceClause
      metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause,
        metadata.localClauseIndex) ∈
        drawing.formula.zipIdx := by
    rw [drawingFormula, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(metadata.clause, metadata.localClauseIndex),
        localClauseMember, rfl⟩
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
    PlanarOneInThreeNoUnits.instantiatedDrawing_isValid
      metadata.sourceClauseIndex metadata.sourceClause
      metadataWidth metadataDistinct
  have selectedOrthogonal :=
    PeriodicOneInThreePositioned.embeddedRoute_orthogonal_of_members
      drawing drawingValid.2.1
      embeddedClauseMember embeddedLiteralMember
  simpa [localRoutes, metadataLookup, drawing] using
    selectedOrthogonal

/-- Every genuine selected local unit-elimination route is simple in the
continuous segment geometry. -/
theorem localRoutes_isSimple_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (localRoutes source clauseIndex literalIndex) := by
  rcases formulaClauseMetadata_lookup_valid
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
    PlanarOneInThreeNoUnits.instantiatedDrawing
      metadata.sourceClauseIndex metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        (clauseGadget metadata.sourceClauseIndex
          metadata.sourceClause).map
            PlanarOneInThreeNoUnits.embedPositionedClause :=
    PlanarOneInThreeNoUnits.instantiatedDrawing_formula
      metadata.sourceClauseIndex metadata.sourceClause
      metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause,
        metadata.localClauseIndex) ∈
        drawing.formula.zipIdx := by
    rw [drawingFormula, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(metadata.clause, metadata.localClauseIndex),
        localClauseMember, rfl⟩
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
    PlanarOneInThreeNoUnits.instantiatedDrawing_isValid
      metadata.sourceClauseIndex metadata.sourceClause
      metadataWidth metadataDistinct
  have selectedSimple :=
    drawing.embeddedRoute_isSimple_of_members
      drawingValid.2.2
      embeddedClauseMember embeddedLiteralMember
  simpa [localRoutes, metadataLookup, drawing] using
    selectedSimple

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
