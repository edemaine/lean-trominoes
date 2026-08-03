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

private theorem embeddedRoute_length_ge_two_of_valid
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (valid : drawing.IsValid)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤ (drawing.routes clauseIndex literalIndex).length := by
  have variableMember : literal.1 ∈ drawing.variableVertices := by
    rw [EmbeddedCNFIncidenceDrawing.variableVertices, List.mem_dedup]
    apply List.mem_flatMap.mpr
    exact ⟨clause, List.fst_mem_of_mem_zipIdx clauseMember,
      List.mem_map.mpr
        ⟨literal, List.fst_mem_of_mem_zipIdx literalMember, rfl⟩⟩
  have variablePositionMember :
      drawing.variablePosition literal.1 ∈
        drawing.variableVertices.map drawing.variablePosition :=
    List.mem_map.mpr ⟨literal.1, variableMember, rfl⟩
  have clausePositionMember :
      clause.position ∈
        drawing.formula.map EmbeddedClause.position :=
    List.mem_map.mpr
      ⟨clause, List.fst_mem_of_mem_zipIdx clauseMember, rfl⟩
  have positionsSeparate :
      ∀ variablePosition ∈
          drawing.variableVertices.map drawing.variablePosition,
        ∀ clausePosition ∈
          drawing.formula.map EmbeddedClause.position,
        variablePosition ≠ clausePosition :=
    (List.nodup_append.mp valid.2.2.2.2.2).2.2
  have endpointsDistinct :
      clause.position ≠ drawing.variablePosition literal.1 := by
    intro equal
    exact
      (positionsSeparate
        (drawing.variablePosition literal.1) variablePositionMember
        clause.position clausePositionMember) equal.symm
  have endpoints :=
    drawing.physicalRoutesMatch valid.1
      clause clauseIndex clauseMember
      literal literalIndex literalMember
  cases routeEqual : drawing.routes clauseIndex literalIndex with
  | nil => simp [routeEqual] at endpoints
  | cons first rest =>
      cases rest with
      | nil =>
          simp [routeEqual] at endpoints
          exact
            (endpointsDistinct
              (endpoints.1.symm.trans endpoints.2)).elim
      | cons second tail => simp

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

/-- Every genuine selected local unit-elimination route contains at least
one edge. -/
theorem localRoutes_length_ge_two_of_members
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
      PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤ (localRoutes source clauseIndex literalIndex).length := by
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
      ⟨(literal, literalIndex), metadataLiteralMember, rfl⟩
  have drawingValid : drawing.IsValid :=
    PlanarOneInThreeNoUnits.instantiatedDrawing_isValid
      metadata.sourceClauseIndex metadata.sourceClause
      metadataWidth metadataDistinct
  simpa [localRoutes, metadataLookup, drawing] using
    embeddedRoute_length_ge_two_of_valid drawing drawingValid
      embeddedClauseMember embeddedLiteralMember

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
