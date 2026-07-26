import LeanTrominoes.PositionedPeriodicCNFAnchorNormalizationDrawing
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodedDegree

/-!
# Exact-one invariance under clause-anchor normalization

Clause-anchor normalization was introduced at the ordinary CNF layer, but
the planar 3DM reduction consumes exact-one formulas.  This file proves that
the same change of periodic gauge preserves the complete list of literal
truth values in every clause translate.  It therefore preserves exact-one
satisfaction and satisfiability under the same plane-wide assignment.

The syntactic occurrence-three and arity-two-or-three promises are also
unchanged, so every hypothesis of the typed planar 3DM reduction transports
to the normalized source.
-/

namespace LeanTrominoes

namespace PeriodicOneInThree

/-- Anchor normalization preserves the ordered list of literal truth values,
after shifting the clause translate by the common anchor. -/
theorem clauseValues_anchorNormalize
    {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clause : PeriodicClause Variable) :
    clauseValues assignment translate clause.anchorNormalize =
      clauseValues assignment
        (Cell.sub translate (PeriodicCNF.clauseAnchor clause)) clause := by
  unfold clauseValues PeriodicClause.anchorNormalize
  rw [List.map_map]
  apply List.map_congr_left
  intro literal literalMember
  simp only [Function.comp_apply,
    PeriodicLiteral.anchorNormalize_atom,
    PeriodicLiteral.anchorNormalize_offset,
    PeriodicLiteral.anchorNormalize_value]
  apply congrArg fun value => value == literal.value
  apply congrArg (assignment literal.atom)
  rcases translate with ⟨translateX, translateY⟩
  rcases literal.offset with ⟨offsetX, offsetY⟩
  rcases PeriodicCNF.clauseAnchor clause with
    ⟨anchorX, anchorY⟩
  apply Prod.ext <;> simp [Cell.add, Cell.sub] <;> ring

/-- Exact-one truth of one normalized clause is the truth of the original
clause at the correspondingly shifted translate. -/
theorem clauseHolds_anchorNormalize_iff
    {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clause : PeriodicClause Variable) :
    ClauseHolds assignment translate clause.anchorNormalize ↔
      ClauseHolds assignment
        (Cell.sub translate (PeriodicCNF.clauseAnchor clause)) clause := by
  simp only [ClauseHolds, clauseValues_anchorNormalize]

/-- A fixed plane-wide assignment satisfies the normalized exact-one formula
exactly when it satisfies the original formula. -/
theorem anchorNormalize_satisfies_iff
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) :
    Satisfies formula.anchorNormalize assignment ↔
      Satisfies formula assignment := by
  constructor
  · intro normalizedSatisfies translate clause clauseMember
    have normalizedMember :
        clause.anchorNormalize ∈ formula.anchorNormalize.clauses :=
      List.mem_map.mpr ⟨clause, clauseMember, rfl⟩
    have normalizedHolds :=
      normalizedSatisfies
        (Cell.add translate (PeriodicCNF.clauseAnchor clause))
        clause.anchorNormalize normalizedMember
    have shifted :=
      (clauseHolds_anchorNormalize_iff assignment
        (Cell.add translate (PeriodicCNF.clauseAnchor clause))
        clause).mp normalizedHolds
    simpa [Cell.add, Cell.sub] using shifted
  · intro originalSatisfies translate normalizedClause
      normalizedMember
    rcases List.mem_map.mp normalizedMember with
      ⟨clause, clauseMember, rfl⟩
    apply
      (clauseHolds_anchorNormalize_iff
        assignment translate clause).mpr
    exact originalSatisfies
      (Cell.sub translate (PeriodicCNF.clauseAnchor clause))
      clause clauseMember

/-- Existence of an exact-one satisfying assignment is invariant under
clause-anchor normalization. -/
theorem anchorNormalize_satisfiable_iff
    {Variable : Type*}
    (formula : PeriodicCNF Variable) :
    Satisfiable formula.anchorNormalize ↔ Satisfiable formula := by
  constructor <;> rintro ⟨assignment, satisfies⟩
  · exact
      ⟨assignment,
        (anchorNormalize_satisfies_iff formula assignment).mp
          satisfies⟩
  · exact
      ⟨assignment,
        (anchorNormalize_satisfies_iff formula assignment).mpr
          satisfies⟩

end PeriodicOneInThree

namespace PeriodicCNF

/-- Clause-anchor normalization preserves every finite-presentation
occurrence bound. -/
theorem anchorNormalize_occurrencesAtMost
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (bound : Nat)
    (occurrences : formula.OccurrencesAtMost bound) :
    formula.anchorNormalize.OccurrencesAtMost bound := by
  intro atom
  simpa [OccurrencesAtMost] using occurrences atom

/-- Clause-anchor normalization preserves the arity-two-or-three promise. -/
theorem anchorNormalize_arityTwoOrThree
    {Variable : Type*} (formula : PeriodicCNF Variable)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree formula) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      formula.anchorNormalize := by
  intro normalizedClause normalizedMember
  rcases List.mem_map.mp normalizedMember with
    ⟨clause, clauseMember, rfl⟩
  simpa using arity clause clauseMember

end PeriodicCNF

namespace PositionedPeriodicCNF

/-- Positioned anchor normalization preserves exact-one satisfiability. -/
theorem anchorNormalize_oneInThree_satisfiable_iff
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    PeriodicOneInThree.Satisfiable
        (source.anchorNormalize placement).erase ↔
      PeriodicOneInThree.Satisfiable source.erase := by
  rw [erase_anchorNormalize,
    PeriodicOneInThree.anchorNormalize_satisfiable_iff]

end PositionedPeriodicCNF

end LeanTrominoes
