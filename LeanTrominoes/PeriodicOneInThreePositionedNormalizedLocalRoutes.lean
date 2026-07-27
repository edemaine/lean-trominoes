import LeanTrominoes.PeriodicOneInThreePositionedLocalRoutes
import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes

/-!
# Anchor-normalized local Figure 9 routes

The certified finite Figure 9 drawings use the displayed physical
coordinates of each source-clause neighborhood.  Periodic incidence drawings
instead store every route in the canonical gauge obtained by subtracting the
generated clause's logical anchor.

This file performs that normalization.  Every genuine route starts at its
canonical generated-clause vertex, ends at the correspondingly normalized
finite-drawing variable endpoint, and remains orthogonal.  For auxiliary
variables that endpoint is already the final periodic variable endpoint; for
inherited source variables it is the boundary point where a global suffix
must be attached.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

open PlanarThreeSAT

/-- The endpoint advertised by the selected finite Figure 9 drawing, put in
the canonical anchor gauge of its generated periodic clause. -/
def normalizedLocalEndpoint
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) : Cell :=
  match (formulaClauseMetadata source)[clauseIndex]? with
  | none => (0, 0)
  | some metadata =>
      match metadata.clause.literals[literalIndex]? with
      | none => (0, 0)
      | some literal =>
          Cell.sub
            ((PlanarOneInThreePositioned.instantiatedDrawing
              metadata.sourceClauseIndex
              metadata.sourceClause).variablePosition literal.atom)
            ((placement source sourcePlacement).translation
              (PeriodicCNF.clauseAnchor
                metadata.clause.literals))

/-- Normalize every metadata-selected local route by its generated clause's
logical anchor. -/
def normalizedLocalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match (formulaClauseMetadata source)[clauseIndex]? with
    | none => []
    | some metadata =>
        PositionedPeriodicCNF.normalizeIncidenceRoute
          (placement source sourcePlacement)
          metadata.clause
          (localRoutes source clauseIndex literalIndex)

/-- Every genuine raw local route meets its displayed generated clause and
the exact variable endpoint selected by the corresponding finite drawing. -/
theorem localRoutes_endpoints_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    ∃ metadata : ClauseMetadata Variable,
      (formulaClauseMetadata source)[clauseIndex]? =
          some metadata ∧
        metadata.clause = clause ∧
        (localRoutes source clauseIndex literalIndex).head? =
          some clause.position ∧
        (localRoutes source clauseIndex literalIndex).getLast? =
          some
            ((PlanarOneInThreePositioned.instantiatedDrawing
              metadata.sourceClauseIndex
              metadata.sourceClause).variablePosition literal.atom) := by
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
    PlanarOneInThreePositioned.instantiatedDrawing
      metadata.sourceClauseIndex metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        (clauseGadget metadata.sourceClauseIndex
          metadata.sourceClause).map
            PlanarOneInThreeNoUnits.embedPositionedClause :=
    PlanarOneInThreePositioned.instantiatedDrawing_formula
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
    PlanarOneInThreePositioned.instantiatedDrawing_isValid
      metadata.sourceClauseIndex metadata.sourceClause
      metadataWidth metadataDistinct
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

/-- Every genuine normalized local Figure 9 route has the exact canonical
generated-clause endpoint and the selected normalized local endpoint. -/
theorem normalizedLocalRoutes_endpoints_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement source sourcePlacement) clause) ∧
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex).getLast? =
        some
          (normalizedLocalEndpoint source sourcePlacement
            clauseIndex literalIndex) := by
  rcases localRoutes_endpoints_of_members
      source sourceWidth sourceDistinct
      clauseMember literalMember with
    ⟨metadata, metadataLookup, clauseEqual,
      localHead, localLast⟩
  subst clause
  constructor
  · simpa [normalizedLocalRoutes, metadataLookup] using
      PositionedPeriodicCNF.normalizeIncidenceRoute_head?
        (placement source sourcePlacement)
        metadata.clause
        (localRoutes source clauseIndex literalIndex)
        localHead
  · have literalLookup :
        metadata.clause.literals[literalIndex]? =
          some literal :=
      (List.mem_zipIdx_iff_getElem?).mp literalMember
    simp [normalizedLocalRoutes, normalizedLocalEndpoint,
      metadataLookup,
      PositionedPeriodicCNF.normalizeIncidenceRoute,
      localLast, literalLookup]

/-- Anchor normalization preserves orthogonality of every genuine selected
Figure 9 route. -/
theorem normalizedLocalRoutes_orthogonal_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex) := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  subst clause
  simpa [normalizedLocalRoutes, metadataLookup] using
    PositionedPeriodicCNF.normalizeIncidenceRoute_orthogonal
      (placement source sourcePlacement)
      metadata.clause
      (localRoutes source clauseIndex literalIndex)
      (localRoutes_orthogonal_of_members
        source sourceWidth sourceDistinct
        clauseMember literalMember)

/-- Anchor normalization preserves the first exit of every genuine local
Figure 9 route. -/
theorem normalizedLocalRoutes_exists_tail_head?_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    ∃ exit,
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex).tail.head? =
        some exit := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  subst clause
  rcases localRoutes_exists_tail_head?_of_members
      source sourceWidth sourceDistinct
      clauseMember literalMember with
    ⟨exit, tailHead⟩
  let normalizePoint : Cell → Cell :=
    fun point =>
      Cell.sub point
        ((placement source sourcePlacement).translation
          (PeriodicCNF.clauseAnchor
            metadata.clause.literals))
  refine ⟨normalizePoint exit, ?_⟩
  simpa [normalizedLocalRoutes, metadataLookup,
    PositionedPeriodicCNF.normalizeIncidenceRoute,
    normalizePoint] using
      List.tail_head?_map normalizePoint tailHead

end PeriodicOneInThreePositioned
end LeanTrominoes
