import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-!
# Clause membership under a variable gauge

Variable gauging maps clauses pointwise without changing their presentation
indices or stored positions.  This small lookup interface avoids unfolding a
large concrete gauged construction merely to recover its source clause.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- A gauged clause recovers the source clause at the same presentation
index. -/
theorem exists_sourceClause_of_variableGaugeClause_mem
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (gauge : Variable → Cell)
    {gaugedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (gaugedMember :
      (gaugedClause, clauseIndex) ∈
        (source.variableGauge gauge).clauses.zipIdx) :
    ∃ sourceClause,
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
      gaugedClause =
        ⟨sourceClause.position,
          sourceClause.literals.variableGauge gauge⟩ := by
  change
    (gaugedClause, clauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨clause.position,
          clause.literals.variableGauge gauge⟩).zipIdx at gaugedMember
  rw [List.zipIdx_map] at gaugedMember
  rcases List.mem_map.mp gaugedMember with
    ⟨taggedClause, taggedClauseMember, gaugedClauseEq⟩
  have clauseIndexEq : taggedClause.2 = clauseIndex :=
    congrArg Prod.snd gaugedClauseEq
  have gaugedClauseValueEq :
      gaugedClause =
        ⟨taggedClause.1.position,
          taggedClause.1.literals.variableGauge gauge⟩ :=
    (congrArg Prod.fst gaugedClauseEq).symm
  subst clauseIndex
  exact ⟨taggedClause.1, taggedClauseMember, gaugedClauseValueEq⟩

end PositionedPeriodicCNF
end LeanTrominoes
