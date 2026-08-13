/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePositionedInheritedRouteFamily
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamily
import LeanTrominoes.PositionedPeriodicCNFLocalRouteSplicingEndpointDirections

/-!
# Terminal directions through exact-one route splicing

This file proves that the Figure 9 and unit-elimination local route prefixes
do not change the variable-side terminal direction of a genuine inherited
incidence suffix.
-/

namespace LeanTrominoes

namespace PeriodicOneInThreePositioned

/-- A genuine inherited Figure 9 route has at least three points whenever
its local prefix and inherited suffix each contain an edge. -/
theorem splicedRoutes_length_ge_three_inherited
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
      PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom)
    (suffixLength :
      2 ≤ (inherited.routes clauseIndex literalIndex).length) :
    3 ≤
      (splicedRoutes source sourcePlacement inherited
        clauseIndex literalIndex).length := by
  let complete :=
    completeRouteSuffixes source sourcePlacement inherited
  have completeEq :
      complete.routes clauseIndex literalIndex =
        inherited.routes clauseIndex literalIndex := by
    change
      PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes
          inherited clauseIndex literalIndex =
        inherited.routes clauseIndex literalIndex
    exact
      PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes_eq_inherited
        inherited clauseMember literalMember sourceAtom literalSource
  rcases normalizedLocalRoutes_exists_tail_head?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember with
    ⟨exit, localTailHead⟩
  have localLength :
      2 ≤
        (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex).length :=
    List.two_le_length_of_tail_head?_eq_some localTailHead
  apply
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes_length_ge_three
      (normalizedLocalRoutes source sourcePlacement)
      complete clauseIndex literalIndex localLength
  simpa [completeEq] using suffixLength

theorem splicedRoutes_lastDirection_inherited
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
      PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom)
    (suffixLength :
      2 ≤ (inherited.routes clauseIndex literalIndex).length) :
    AxisDirection.polylineLastDirection
        (splicedRoutes source sourcePlacement inherited
          clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (inherited.routes clauseIndex literalIndex) := by
  let complete :=
    completeRouteSuffixes source sourcePlacement inherited
  have completeEq :
      complete.routes clauseIndex literalIndex =
        inherited.routes clauseIndex literalIndex := by
    change
      PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes
          inherited clauseIndex literalIndex =
        inherited.routes clauseIndex literalIndex
    exact
      PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes_eq_inherited
        inherited clauseMember literalMember sourceAtom literalSource
  have localEndpoints :=
    normalizedLocalRoutes_endpoints_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember
  have completeEndpoints :=
    complete.endpoints clause clauseIndex clauseMember
      literal literalIndex literalMember
  calc
    AxisDirection.polylineLastDirection
        (splicedRoutes source sourcePlacement inherited
          clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (complete.routes clauseIndex literalIndex) := by
          change
            AxisDirection.polylineLastDirection
                (PositionedPeriodicCNF.spliceLocalIncidenceRoutes
                  (normalizedLocalRoutes source sourcePlacement)
                  complete clauseIndex literalIndex) =
              AxisDirection.polylineLastDirection
                (complete.routes clauseIndex literalIndex)
          exact
            PositionedPeriodicCNF.spliceLocalIncidenceRoutes_lastDirection
              (normalizedLocalRoutes source sourcePlacement)
              complete clauseIndex literalIndex
              (normalizedLocalEndpoint source sourcePlacement
                clauseIndex literalIndex)
              localEndpoints.2 completeEndpoints.1
              (by simpa [completeEq] using suffixLength)
    _ = AxisDirection.polylineLastDirection
          (inherited.routes clauseIndex literalIndex) := by
      rw [completeEq]

end PeriodicOneInThreePositioned

namespace PeriodicOneInThreeNoUnitsPositioned

theorem splicedRoutes_lastDirection_inherited
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
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom)
    (suffixLength :
      2 ≤ (inherited.routes clauseIndex literalIndex).length) :
    AxisDirection.polylineLastDirection
        (splicedRoutes source sourcePlacement inherited
          clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (inherited.routes clauseIndex literalIndex) := by
  let complete :=
    completeRouteSuffixes source sourcePlacement inherited
  have completeEq :
      complete.routes clauseIndex literalIndex =
        inherited.routes clauseIndex literalIndex := by
    change
      PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes
          inherited clauseIndex literalIndex =
        inherited.routes clauseIndex literalIndex
    exact
      PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes_eq_inherited
        inherited clauseMember literalMember sourceAtom literalSource
  have localEndpoints :=
    normalizedLocalRoutes_endpoints_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember
  have completeEndpoints :=
    complete.endpoints clause clauseIndex clauseMember
      literal literalIndex literalMember
  calc
    AxisDirection.polylineLastDirection
        (splicedRoutes source sourcePlacement inherited
          clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (complete.routes clauseIndex literalIndex) := by
          change
            AxisDirection.polylineLastDirection
                (PositionedPeriodicCNF.spliceLocalIncidenceRoutes
                  (normalizedLocalRoutes source sourcePlacement)
                  complete clauseIndex literalIndex) =
              AxisDirection.polylineLastDirection
                (complete.routes clauseIndex literalIndex)
          exact
            PositionedPeriodicCNF.spliceLocalIncidenceRoutes_lastDirection
              (normalizedLocalRoutes source sourcePlacement)
              complete clauseIndex literalIndex
              (normalizedLocalEndpoint source sourcePlacement
                clauseIndex literalIndex)
              localEndpoints.2 completeEndpoints.1
              (by simpa [completeEq] using suffixLength)
    _ = AxisDirection.polylineLastDirection
          (inherited.routes clauseIndex literalIndex) := by
      rw [completeEq]

end PeriodicOneInThreeNoUnitsPositioned

end LeanTrominoes
