/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasure
import LeanTrominoes.PeriodicOneInThreePositionedAuxiliaryEndpoints
import LeanTrominoes.PositionedPeriodicCNFLocalRouteSplicingEndpointDirections

/-!
# Endpoint isolation for Figure 9 auxiliary routes

Fresh Figure 9 auxiliaries already sit at their final local gadget positions.
Their canonical suffix is therefore a singleton, so the complete spliced route
is exactly the simple normalized local route.  This file records that equality
and the two endpoint-isolation facts needed to preserve route orders through
loop erasure.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

/-- A genuine fresh-auxiliary route gains no points from Figure 9 route
splicing. -/
theorem splicedRoutes_eq_normalizedLocalRoutes_of_auxiliary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (inherited :
      PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
        (formula source)
        (placement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (auxiliary :
      (Nat × PeriodicClause Variable) × OneInThreeAux)
    (literalAuxiliary : literal.atom = .inr auxiliary) :
    splicedRoutes source sourcePlacement inherited
        clauseIndex literalIndex =
      normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex := by
  let complete :=
    completeRouteSuffixes source sourcePlacement inherited
  have suffixSingleton :
      complete.routes clauseIndex literalIndex =
        [normalizedLocalEndpoint source sourcePlacement
          clauseIndex literalIndex] := by
    change
      PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes
          inherited clauseIndex literalIndex =
        [normalizedLocalEndpoint source sourcePlacement
          clauseIndex literalIndex]
    exact
      PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes_eq_auxiliary
        inherited clauseMember literalMember
        auxiliary literalAuxiliary
  change
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes
        (normalizedLocalRoutes source sourcePlacement)
        complete clauseIndex literalIndex =
      normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex
  exact
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes_eq_local_of_suffix_singleton
      (normalizedLocalRoutes source sourcePlacement)
      complete clauseIndex literalIndex suffixSingleton

/-- Both terminal points of a genuine fresh-auxiliary Figure 9 route remain
isolated after unit subdivision. -/
theorem splicedRoutes_endpointIsolation_of_auxiliary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (inherited :
      PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
        (formula source)
        (placement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (auxiliary :
      (Nat × PeriodicClause Variable) × OneInThreeAux)
    (literalAuxiliary : literal.atom = .inr auxiliary) :
    AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline
          (splicedRoutes source sourcePlacement inherited
            clauseIndex literalIndex)) ∧
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline
          (splicedRoutes source sourcePlacement inherited
            clauseIndex literalIndex)) := by
  rw [splicedRoutes_eq_normalizedLocalRoutes_of_auxiliary
    source sourcePlacement inherited clauseMember literalMember
    auxiliary literalAuxiliary]
  have orthogonal :=
    normalizedLocalRoutes_orthogonal_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember
  have simple :=
    normalizedLocalRoutes_isSimple_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember
  exact
    ⟨AxisDirection.headNotInTail_unitSubdividePolyline_of_simple
        orthogonal simple,
      AxisDirection.lastNotInDropLast_unitSubdividePolyline_of_simple
        orthogonal simple⟩

end PeriodicOneInThreePositioned
end LeanTrominoes
