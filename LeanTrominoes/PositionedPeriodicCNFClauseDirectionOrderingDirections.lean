/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering

/-! # Direction words through clockwise clause ordering -/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

open Gadget

/-- Every valid clockwise-ordered incidence recovers one original literal
index, and its canonical anchor translation preserves that source route's
complete direction word. -/
theorem exists_sourceLiteral_directionWord_of_orderedLiteral_mem
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {orderedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (orderedClause, clauseIndex) ∈
        (orderClausesByRouteDirection source routes).clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ orderedClause.literals.zipIdx) :
    ∃ sourceClause sourceLiteral sourceLiteralIndex,
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx ∧
      literal = sourceLiteral ∧
      unitSubdivisionDirections
          (orderCanonicalRoutesByClauseDirection source placement routes
            clauseIndex literalIndex) =
        unitSubdivisionDirections
          (routes clauseIndex sourceLiteralIndex) := by
  rcases exists_sourceLiteral_of_orderedLiteral_mem
      routes clauseMember literalMember with
    ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
      sourceClauseMember, sourceLiteralMember,
      _orderedClauseEq, literalEq, orderedRouteEq⟩
  refine ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
    sourceClauseMember, sourceLiteralMember, literalEq, ?_⟩
  have sourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp sourceClauseMember
  unfold orderCanonicalRoutesByClauseDirection
  rw [sourceClauseLookup, orderedRouteEq]
  exact unitSubdivisionDirections_translatePolyline _ _

end PositionedPeriodicCNF
end LeanTrominoes
