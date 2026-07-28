import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Tagged route lookup in positioned periodic incidence drawings

The route list of an incidence drawing is a map over its metadata-rich
incidence enumeration.  This module preserves the global flat route index
while recovering the corresponding positioned clause and literal
coordinates.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- A route occurrence tagged in the flat drawing list recovers the
metadata-rich incidence at the same flat index and its two presentation
coordinates. -/
theorem exists_incidenceCoordinates_of_taggedRoute
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (taggedRoute : List Cell × Nat)
    (taggedRouteMember :
      taggedRoute ∈
        (incidenceDrawing source placement routes).edgeRoutes.zipIdx) :
    ∃ taggedIncidence :
        CNFIncidence Variable × Nat,
      taggedIncidence ∈
          (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx ∧
        ∃ positionedClause : PositionedPeriodicClause Variable,
          ∃ literal : PeriodicLiteral Variable,
            (positionedClause,
                taggedIncidence.1.clauseIndex) ∈
              source.clauses.zipIdx ∧
            (literal, taggedIncidence.1.literalIndex) ∈
              positionedClause.literals.zipIdx ∧
            taggedRoute.1 =
              routes taggedIncidence.1.clauseIndex
                taggedIncidence.1.literalIndex ∧
            taggedIncidence.2 = taggedRoute.2 := by
  change
    taggedRoute ∈
      (incidenceEdgeRoutes source routes).zipIdx
      at taggedRouteMember
  rw [incidenceEdgeRoutes_eq_metadata_map,
    List.zipIdx_map] at taggedRouteMember
  rcases List.mem_map.mp taggedRouteMember with
    ⟨taggedIncidence, taggedIncidenceMember,
      taggedRouteEq⟩
  rcases incidenceMetadata_of_tagged
      source taggedIncidenceMember with
    ⟨positionedClause, literal,
      positionedClauseMember, literalMember, _⟩
  exact
    ⟨taggedIncidence, taggedIncidenceMember,
      positionedClause, literal,
      positionedClauseMember, literalMember,
      (congrArg Prod.fst taggedRouteEq).symm,
      congrArg Prod.snd taggedRouteEq⟩

end PositionedPeriodicCNF
end LeanTrominoes
