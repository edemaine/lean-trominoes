/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseRouteOrder
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering
import LeanTrominoes.PositionedPeriodicCNFTaggedRouteLookup

/-!
# Final ordering of unit-elimination clauses

A ternary unit-elimination clause has route exits south, west, and east at
literal indices `0`, `1`, and `2`.  Stable sorting by clockwise rank beginning
at east therefore gives the exact order `2, 0, 1`.  In particular, the old
third literal becomes the new canonical anchor.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

variable {Variable : Type*} [DecidableEq Variable]

/-- Read the unit-elimination route-order condition at a genuine positioned
clause/literal coordinate. -/
theorem TernaryClauseRoutesInUnitEliminationOrder.firstDirection_of_members
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (ordered : source.TernaryClauseRoutesInUnitEliminationOrder routes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    (arity : clause.literals.length = 3)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (routes clauseIndex literalIndex) =
      AxisDirection.unitEliminationClauseExitDirection literalIndex := by
  rcases exists_taggedIncidenceRoute_of_positioned_members
      source placement routes clauseMember literalMember with
    ⟨routeIndex, taggedMember, _routeMember⟩
  exact ordered
    (⟨clauseIndex, clause.literals, literalIndex, literal⟩, routeIndex)
    taggedMember arity

/-- The stable clockwise tag order of a ternary unit-elimination clause is
exactly old indices `2, 0, 1`. -/
theorem clauseLiteralOrder_eq_two_zero_one_of_unitEliminationOrder
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (ordered : source.TernaryClauseRoutesInUnitEliminationOrder routes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {first second third : PeriodicLiteral Variable}
    (literalsEq : clause.literals = [first, second, third]) :
    clauseLiteralOrder routes clauseIndex clause =
      [(third, 2), (first, 0), (second, 1)] := by
  have arity : clause.literals.length = 3 := by simp [literalsEq]
  have firstDirection :=
    ordered.firstDirection_of_members
      (placement := placement) clauseMember arity
      (literal := first) (literalIndex := 0)
      (by simp [literalsEq])
  have secondDirection :=
    ordered.firstDirection_of_members
      (placement := placement) clauseMember arity
      (literal := second) (literalIndex := 1)
      (by simp [literalsEq])
  have thirdDirection :=
    ordered.firstDirection_of_members
      (placement := placement) clauseMember arity
      (literal := third) (literalIndex := 2)
      (by simp [literalsEq])
  simp [clauseLiteralOrder, clauseLiteralDirectionLE,
    clauseLiteralDirectionRank, literalsEq,
    firstDirection, secondDirection, thirdDirection,
    AxisDirection.unitEliminationClauseExitDirection,
    AxisDirection.clockwiseRank]

/-- Consequently the displayed literal list after final ordering is the
cyclic order `old third, old first, old second`. -/
theorem orderClauseByRouteDirection_literals_eq_two_zero_one_of_unitEliminationOrder
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (ordered : source.TernaryClauseRoutesInUnitEliminationOrder routes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {first second third : PeriodicLiteral Variable}
    (literalsEq : clause.literals = [first, second, third]) :
    (orderClauseByRouteDirection routes clauseIndex clause).literals =
      [third, first, second] := by
  simp [orderClauseByRouteDirection,
    clauseLiteralOrder_eq_two_zero_one_of_unitEliminationOrder
      (placement := placement) ordered clauseMember literalsEq]

/-- The final reordered ternary clause is canonically anchored at its old
third literal. -/
theorem orderClauseByRouteDirection_anchor_eq_third_offset_of_unitEliminationOrder
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (ordered : source.TernaryClauseRoutesInUnitEliminationOrder routes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {first second third : PeriodicLiteral Variable}
    (literalsEq : clause.literals = [first, second, third]) :
    PeriodicCNF.clauseAnchor
        (orderClauseByRouteDirection
          routes clauseIndex clause).literals =
      third.offset := by
  rw [orderClauseByRouteDirection_literals_eq_two_zero_one_of_unitEliminationOrder
    (placement := placement) ordered clauseMember literalsEq]
  rfl

/-- The canonical route transport realizes the corresponding cyclic order
of first directions: east, south, west. -/
theorem orderCanonicalRoutesByClauseDirection_ternaryClockwise_of_unitEliminationOrder
    {source : PositionedPeriodicCNF Variable}
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (ordered : source.TernaryClauseRoutesInUnitEliminationOrder routes) :
    TernaryClauseRoutesInClockwiseOrder
      (orderClausesByRouteDirection source routes)
      (orderCanonicalRoutesByClauseDirection source placement routes) := by
  intro orderedClause clauseIndex orderedClauseMember arity
  rcases exists_sourceClause_of_orderedClause_mem
      routes orderedClauseMember with
    ⟨sourceClause, sourceClauseMember, orderedClauseEq⟩
  have sourceArity : sourceClause.literals.length = 3 := by
    rw [← orderClauseByRouteDirection_length
      routes clauseIndex sourceClause, ← orderedClauseEq]
    exact arity
  rcases List.length_eq_three.mp sourceArity with
    ⟨first, second, third, literalsEq⟩
  have orderEq :=
    clauseLiteralOrder_eq_two_zero_one_of_unitEliminationOrder
      (placement := placement) ordered sourceClauseMember literalsEq
  have direction0 :=
    orderCanonicalRoutesByClauseDirection_firstDirection_of_lookup
      placement routes sourceClauseMember
      (literalIndex := 0) (taggedLiteral := (third, 2))
      (by simp [orderEq])
  have direction1 :=
    orderCanonicalRoutesByClauseDirection_firstDirection_of_lookup
      placement routes sourceClauseMember
      (literalIndex := 1) (taggedLiteral := (first, 0))
      (by simp [orderEq])
  have direction2 :=
    orderCanonicalRoutesByClauseDirection_firstDirection_of_lookup
      placement routes sourceClauseMember
      (literalIndex := 2) (taggedLiteral := (second, 1))
      (by simp [orderEq])
  have sourceDirection0 :=
    ordered.firstDirection_of_members
      (placement := placement) sourceClauseMember sourceArity
      (literal := first) (literalIndex := 0)
      (by simp [literalsEq])
  have sourceDirection1 :=
    ordered.firstDirection_of_members
      (placement := placement) sourceClauseMember sourceArity
      (literal := second) (literalIndex := 1)
      (by simp [literalsEq])
  have sourceDirection2 :=
    ordered.firstDirection_of_members
      (placement := placement) sourceClauseMember sourceArity
      (literal := third) (literalIndex := 2)
      (by simp [literalsEq])
  rw [direction0, direction1, direction2,
    sourceDirection2, sourceDirection0, sourceDirection1]
  native_decide

end PositionedPeriodicCNF
end LeanTrominoes
