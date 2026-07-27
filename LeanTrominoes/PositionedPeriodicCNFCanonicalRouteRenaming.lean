import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Canonical incidence routes under variable renaming

Renaming a positioned periodic formula changes only literal atoms.  If a
target placement assigns each renamed atom the same physical position and
retains the same period, an existing route family keeps its canonical
clause and literal endpoints.  Orthogonality is unchanged because the route
lists themselves are reused verbatim.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Pointwise canonical route endpoints survive a position-preserving
variable renaming. -/
theorem canonicalIncidenceRoutes_endpoints_rename
    {Source Target : Type*}
    (source : PositionedPeriodicCNF Source)
    (sourcePlacement : PeriodicVariablePlacement Source)
    (targetPlacement : PeriodicVariablePlacement Target)
    (routes : IncidenceRoutes)
    (variableMap : Source → Target)
    (sourceEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (routes sourceClauseIndex sourceLiteralIndex).head? =
              some
                (canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (routes sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (canonicalLiteralPosition
                  sourcePlacement sourceClause sourceLiteral))
    (positionsMatch :
      ∀ atom,
        targetPlacement.position (variableMap atom) =
          sourcePlacement.position atom)
    (periodsMatch :
      targetPlacement.period = sourcePlacement.period)
    {targetClause : PositionedPeriodicClause Target}
    {clauseIndex : Nat}
    (targetClauseMember :
      (targetClause, clauseIndex) ∈
        (source.rename variableMap).clauses.zipIdx)
    {targetLiteral : PeriodicLiteral Target}
    {literalIndex : Nat}
    (targetLiteralMember :
      (targetLiteral, literalIndex) ∈
        targetClause.literals.zipIdx) :
    (routes clauseIndex literalIndex).head? =
        some
          (canonicalClausePosition
            targetPlacement targetClause) ∧
      (routes clauseIndex literalIndex).getLast? =
        some
          (canonicalLiteralPosition
            targetPlacement targetClause targetLiteral) := by
  change
    (targetClause, clauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨clause.position, clause.literals.map fun literal =>
          ⟨variableMap literal.atom,
            literal.offset, literal.value⟩⟩).zipIdx
    at targetClauseMember
  rw [List.zipIdx_map] at targetClauseMember
  rcases List.mem_map.mp targetClauseMember with
    ⟨taggedSourceClause, taggedSourceClauseMember,
      targetClauseEqual⟩
  have clauseIndexEqual :
      taggedSourceClause.2 = clauseIndex :=
    congrArg Prod.snd targetClauseEqual
  have targetClauseValueEqual :
      targetClause =
        ⟨taggedSourceClause.1.position,
          taggedSourceClause.1.literals.map fun literal =>
            ⟨variableMap literal.atom,
              literal.offset, literal.value⟩⟩ := by
    exact (congrArg Prod.fst targetClauseEqual).symm
  subst clauseIndex
  subst targetClause
  change
    (targetLiteral, literalIndex) ∈
      (taggedSourceClause.1.literals.map fun literal =>
        ⟨variableMap literal.atom,
          literal.offset, literal.value⟩).zipIdx
    at targetLiteralMember
  rw [List.zipIdx_map] at targetLiteralMember
  rcases List.mem_map.mp targetLiteralMember with
    ⟨taggedSourceLiteral, taggedSourceLiteralMember,
      targetLiteralEqual⟩
  have literalIndexEqual :
      taggedSourceLiteral.2 = literalIndex :=
    congrArg Prod.snd targetLiteralEqual
  have targetLiteralValueEqual :
      targetLiteral =
        ⟨variableMap taggedSourceLiteral.1.atom,
          taggedSourceLiteral.1.offset,
          taggedSourceLiteral.1.value⟩ := by
    exact (congrArg Prod.fst targetLiteralEqual).symm
  subst literalIndex
  subst targetLiteral
  have anchorEqual :
      PeriodicCNF.clauseAnchor
          (taggedSourceClause.1.literals.map fun literal =>
            ⟨variableMap literal.atom,
              literal.offset, literal.value⟩) =
        PeriodicCNF.clauseAnchor
          taggedSourceClause.1.literals := by
    cases taggedSourceClause.1.literals <;> rfl
  have endpoints :=
    sourceEndpoints
      taggedSourceClause.1 taggedSourceClause.2
      taggedSourceClauseMember
      taggedSourceLiteral.1 taggedSourceLiteral.2
      taggedSourceLiteralMember
  constructor
  · simpa [canonicalClausePosition,
      PeriodicVariablePlacement.translation,
      periodsMatch, anchorEqual] using endpoints.1
  · rw [endpoints.2]
    apply congrArg some
    apply Prod.ext <;>
    simp [canonicalLiteralPosition,
      PeriodicVariablePlacement.translation,
      positionsMatch, periodsMatch, anchorEqual,
      Cell.add, Cell.sub, Cell.scale]

/-- Pointwise route orthogonality survives variable renaming because the
route lookup is unchanged. -/
theorem canonicalIncidenceRoutes_orthogonal_rename
    {Source Target : Type*}
    (source : PositionedPeriodicCNF Source)
    (routes : IncidenceRoutes)
    (variableMap : Source → Target)
    (sourceOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes sourceClauseIndex sourceLiteralIndex))
    {targetClause : PositionedPeriodicClause Target}
    {clauseIndex : Nat}
    (targetClauseMember :
      (targetClause, clauseIndex) ∈
        (source.rename variableMap).clauses.zipIdx)
    {targetLiteral : PeriodicLiteral Target}
    {literalIndex : Nat}
    (targetLiteralMember :
      (targetLiteral, literalIndex) ∈
        targetClause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (routes clauseIndex literalIndex) := by
  change
    (targetClause, clauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨clause.position, clause.literals.map fun literal =>
          ⟨variableMap literal.atom,
            literal.offset, literal.value⟩⟩).zipIdx
    at targetClauseMember
  rw [List.zipIdx_map] at targetClauseMember
  rcases List.mem_map.mp targetClauseMember with
    ⟨taggedSourceClause, taggedSourceClauseMember,
      targetClauseEqual⟩
  have clauseIndexEqual :
      taggedSourceClause.2 = clauseIndex :=
    congrArg Prod.snd targetClauseEqual
  have targetClauseValueEqual :
      targetClause =
        ⟨taggedSourceClause.1.position,
          taggedSourceClause.1.literals.map fun literal =>
            ⟨variableMap literal.atom,
              literal.offset, literal.value⟩⟩ := by
    exact (congrArg Prod.fst targetClauseEqual).symm
  subst clauseIndex
  subst targetClause
  change
    (targetLiteral, literalIndex) ∈
      (taggedSourceClause.1.literals.map fun literal =>
        ⟨variableMap literal.atom,
          literal.offset, literal.value⟩).zipIdx
    at targetLiteralMember
  rw [List.zipIdx_map] at targetLiteralMember
  rcases List.mem_map.mp targetLiteralMember with
    ⟨taggedSourceLiteral, taggedSourceLiteralMember,
      targetLiteralEqual⟩
  have literalIndexEqual :
      taggedSourceLiteral.2 = literalIndex :=
    congrArg Prod.snd targetLiteralEqual
  subst literalIndex
  exact
    sourceOrthogonal
      taggedSourceClause.1 taggedSourceClause.2
      taggedSourceClauseMember
      taggedSourceLiteral.1 taggedSourceLiteral.2
      taggedSourceLiteralMember

end PositionedPeriodicCNF
end LeanTrominoes
