import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.PositionedPeriodicCNFSumRouteSuffixes

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Completing a sum-typed suffix family leaves every inherited source
suffix unchanged. -/
theorem completeSumIncidenceRouteSuffixesRoutes_eq_inherited
    {Source Auxiliary : Type*}
    {target : PositionedPeriodicCNF (Sum Source Auxiliary)}
    {placement :
      PeriodicVariablePlacement (Sum Source Auxiliary)}
    {splicePoint : Nat → Nat → Cell}
    (inherited :
      InheritedCanonicalIncidenceRouteSuffixes
        target placement splicePoint)
    {clause : PositionedPeriodicClause (Sum Source Auxiliary)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ target.clauses.zipIdx)
    {literal : PeriodicLiteral (Sum Source Auxiliary)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Source)
    (literalSource : literal.atom = .inl sourceAtom) :
    completeSumIncidenceRouteSuffixesRoutes inherited
        clauseIndex literalIndex =
      inherited.routes clauseIndex literalIndex := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [completeSumIncidenceRouteSuffixesRoutes,
    clauseLookup, literalLookup, literalSource]

/-- A local clause prefix does not change the final direction of a
nondegenerate canonical suffix. -/
theorem spliceLocalIncidenceRoutes_lastDirection
    (localRoutes : IncidenceRoutes)
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {splicePoint : Nat → Nat → Cell}
    (suffixes :
      CanonicalIncidenceRouteSuffixes
        source placement splicePoint)
    (clauseIndex literalIndex : Nat)
    (middle : Cell)
    (localLast :
      (localRoutes clauseIndex literalIndex).getLast? =
        some middle)
    (suffixHead :
      (suffixes.routes clauseIndex literalIndex).head? =
        some middle)
    (suffixLength :
      2 ≤ (suffixes.routes clauseIndex literalIndex).length) :
    AxisDirection.polylineLastDirection
        (spliceLocalIncidenceRoutes localRoutes suffixes
          clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (suffixes.routes clauseIndex literalIndex) := by
  exact AxisDirection.polylineLastDirection_joinAtEndpoint
    localLast suffixHead suffixLength

end PositionedPeriodicCNF
end LeanTrominoes
