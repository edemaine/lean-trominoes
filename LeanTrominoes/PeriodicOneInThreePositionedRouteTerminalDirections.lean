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
