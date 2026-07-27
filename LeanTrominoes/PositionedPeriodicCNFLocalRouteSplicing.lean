import LeanTrominoes.OrthogonalPolylineJoin
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Splicing local positioned-CNF routes to canonical suffixes

Constant-size clause replacements provide a local route from each generated
clause to a boundary or auxiliary endpoint.  Inherited variables additionally
need a suffix from that local endpoint to the final periodic literal vertex.

This file packages that suffix obligation independently of any particular
gadget and proves the common splice theorem.  Both component routes are in
the generated clause's canonical anchor gauge.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- One endpoint-compatible orthogonal suffix for every genuine incidence.
The route begins at a caller-supplied local splice point and ends at the
canonical periodic literal endpoint. -/
structure CanonicalIncidenceRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (splicePoint : Nat → Nat → Cell) where
  routes : IncidenceRoutes
  endpoints :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        (routes clauseIndex literalIndex).head? =
            some (splicePoint clauseIndex literalIndex) ∧
          (routes clauseIndex literalIndex).getLast? =
            some
              (canonicalLiteralPosition
                placement clause literal)
  orthogonal :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        PeriodicOrthocrossing.OrthogonalPolyline
          (routes clauseIndex literalIndex)

/-- Join a local clause-to-boundary route to its canonical boundary-to-
variable suffix. -/
def spliceLocalIncidenceRoutes
    (localRoutes : IncidenceRoutes)
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {splicePoint : Nat → Nat → Cell}
    (suffixes :
      CanonicalIncidenceRouteSuffixes
        source placement splicePoint) :
    IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    joinAtEndpoint
      (localRoutes clauseIndex literalIndex)
      (suffixes.routes clauseIndex literalIndex)

/-- Matching local and suffix certificates give a complete canonical route
with both outer endpoints and preserved orthogonality. -/
theorem spliceLocalIncidenceRoutes_valid_of_members
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {splicePoint : Nat → Nat → Cell}
    (localRoutes : IncidenceRoutes)
    (suffixes :
      CanonicalIncidenceRouteSuffixes
        source placement splicePoint)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (localEndpoints :
      (localRoutes clauseIndex literalIndex).head? =
          some (canonicalClausePosition placement clause) ∧
        (localRoutes clauseIndex literalIndex).getLast? =
          some (splicePoint clauseIndex literalIndex))
    (localOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (localRoutes clauseIndex literalIndex)) :
    (spliceLocalIncidenceRoutes localRoutes suffixes
        clauseIndex literalIndex).head? =
        some (canonicalClausePosition placement clause) ∧
      (spliceLocalIncidenceRoutes localRoutes suffixes
        clauseIndex literalIndex).getLast? =
        some
          (canonicalLiteralPosition placement clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (spliceLocalIncidenceRoutes localRoutes suffixes
          clauseIndex literalIndex) := by
  have suffixEndpoints :=
    suffixes.endpoints clause clauseIndex clauseMember
      literal literalIndex literalMember
  have suffixOrthogonal :=
    suffixes.orthogonal clause clauseIndex clauseMember
      literal literalIndex literalMember
  constructor
  · exact joinAtEndpoint_head? localEndpoints.1
  constructor
  · exact joinAtEndpoint_getLast?
      localEndpoints.2 suffixEndpoints.1 suffixEndpoints.2
  · exact localOrthogonal.joinAtEndpoint
      suffixOrthogonal localEndpoints.2 suffixEndpoints.1

end PositionedPeriodicCNF
end LeanTrominoes
