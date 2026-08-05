import LeanTrominoes.PositionedPeriodicCNFRebasedRouteRadiusBounds
import LeanTrominoes.PositionedPeriodicCNFScaling

/-!
# Scaling variable-centered rebased-route bounds

Uniform positive-coordinate refinement scales the radius, variable center,
and every point of a rebased incidence route by the same factor.  Thus a
one-period variable-centered bound remains a one-period bound for the scaled
placement.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit

namespace PeriodicEightOccurrenceSplit

/-- Coordinate-radius containment scales uniformly. -/
theorem WithinCoordinateRadius.scale
    {radius : Nat} {center point : Cell}
    (bounded : WithinCoordinateRadius radius center point)
    (factor : Nat) :
    WithinCoordinateRadius (factor * radius)
      (Cell.scale factor center) (Cell.scale factor point) := by
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [WithinCoordinateRadius, Cell.scale] at bounded ⊢
  constructor
  · rw [← mul_sub, Int.natAbs_mul]
    exact Nat.mul_le_mul_left factor bounded.1
  · rw [← mul_sub, Int.natAbs_mul]
    exact Nat.mul_le_mul_left factor bounded.2

end PeriodicEightOccurrenceSplit

namespace PositionedPeriodicCNF

/-- Scaling a positioned formula, placement, and route family preserves the
raw variable-centered one-period certificate. -/
theorem RebasedIncidenceRoutesWithinVariablePeriod.scale
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (bounds :
      RebasedIncidenceRoutesWithinVariablePeriod
        source placement routes)
    (factor : Nat) :
    RebasedIncidenceRoutesWithinVariablePeriod
      (source.scale factor)
      (placement.scale factor)
      (scaleIncidenceRoutes factor routes) := by
  intro scaledClause clauseIndex scaledClauseMember
    literal literalIndex literalMember point pointMember
  rw [scale_clauses, List.zipIdx_map] at scaledClauseMember
  rcases List.mem_map.mp scaledClauseMember with
    ⟨taggedClause, taggedClauseMember, scaledTaggedClauseEq⟩
  have clauseIndexEq : taggedClause.2 = clauseIndex :=
    congrArg Prod.snd scaledTaggedClauseEq
  subst clauseIndex
  have scaledClauseEq :
      scaledClause = taggedClause.1.scale factor :=
    (congrArg Prod.fst scaledTaggedClauseEq).symm
  subst scaledClause
  change
    (literal, literalIndex) ∈ taggedClause.1.literals.zipIdx
    at literalMember
  simp only [PeriodicVariablePlacement.translation_scale,
    scaleIncidenceRoutes, List.reverse_map,
    PeriodicOrthocrossing.translatePolyline, scalePolyline,
    List.map_map, Function.comp_def, Cell.scale_add] at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨sourcePoint, sourcePointMember, rfl⟩
  have sourceBounded :=
    bounds taggedClause.1 taggedClause.2 taggedClauseMember
      literal literalIndex literalMember sourcePoint sourcePointMember
  simpa using sourceBounded.scale factor

end PositionedPeriodicCNF
end LeanTrominoes
