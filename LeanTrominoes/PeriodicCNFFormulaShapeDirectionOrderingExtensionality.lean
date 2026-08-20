/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaData

/-! # Extensionality of formula direction descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeDirectionOrdering

/-- Clause descriptor tokens may be computed from erased literal lists using
arbitrary dummy displayed positions. -/
theorem clauseTokens_eq_erased {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    source.clauses.zipIdx.map (fun taggedClause =>
        Token.clause
          (DirectedClauseProfile.ofClause routes
            taggedClause.2 taggedClause.1)) =
      source.erase.clauses.zipIdx.map (fun taggedClause =>
        Token.clause
          (DirectedClauseProfile.ofClause routes
            taggedClause.2 ⟨(0, 0), taggedClause.1⟩)) := by
  unfold PositionedPeriodicCNF.erase
  rw [List.zipIdx_map, List.map_map]
  apply List.map_congr_left
  intro taggedClause _taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  rfl

/-- Canonical formula direction descriptors depend only on the erased clause
list and the first direction returned at each pair of presentation indices. -/
theorem ofFormula_eq_of_erase_clauses_eq_of_firstDirections_eq
    {Variable : Type} [DecidableEq Variable]
    (first second : PositionedPeriodicCNF Variable)
    (firstRoutes secondRoutes :
      PositionedPeriodicCNF.IncidenceRoutes)
    (clausesEq : first.erase.clauses = second.erase.clauses)
    (directionsEq : ∀ clauseIndex literalIndex,
      AxisDirection.polylineFirstDirection
          (firstRoutes clauseIndex literalIndex) =
        AxisDirection.polylineFirstDirection
          (secondRoutes clauseIndex literalIndex)) :
    ofFormula first firstRoutes = ofFormula second secondRoutes := by
  unfold ofFormula
  rw [clauseTokens_eq_erased, clauseTokens_eq_erased, clausesEq]
  apply congrArg₂ (fun clauses variableTokens => clauses ++ variableTokens)
  · apply List.map_congr_left
    intro taggedClause _taggedClauseMember
    apply congrArg Token.clause
    unfold DirectedClauseProfile.ofClause annotatedLiterals
    apply congrArg DirectedClauseProfile.ofList
    apply List.map_congr_left
    intro taggedLiteral _taggedLiteralMember
    apply Prod.ext
    · rfl
    · exact directionsEq taggedClause.2 taggedLiteral.2
  · unfold PeriodicCNF.variableOccurrences
    rw [clausesEq]

end FormulaShapeDirectionOrdering
end PeriodicCNF
end LeanTrominoes
