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
  simp only [PositionedPeriodicClause.scale_literals,
    PeriodicVariablePlacement.translation_scale,
    scaleIncidenceRoutes,
    PeriodicOrthocrossing.translatePolyline, scalePolyline]
    at pointMember
  rw [← List.map_reverse] at pointMember
  simp only [List.map_map, Function.comp_def, ← Cell.scale_add]
    at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨sourcePoint, sourcePointMember, rfl⟩
  have sourceRebasedMember :
      Cell.add
          (placement.translation
            (Cell.sub
              (PeriodicCNF.clauseAnchor taggedClause.1.literals)
              literal.offset))
          sourcePoint ∈
        PeriodicOrthocrossing.translatePolyline
          (placement.translation
            (Cell.sub
              (PeriodicCNF.clauseAnchor taggedClause.1.literals)
              literal.offset))
          (routes taggedClause.2 literalIndex).reverse := by
    unfold PeriodicOrthocrossing.translatePolyline
    exact List.mem_map.mpr ⟨sourcePoint, sourcePointMember, rfl⟩
  have sourceBounded :=
    bounds taggedClause.1 taggedClause.2 taggedClauseMember
      literal literalIndex literalMember
      (Cell.add
        (placement.translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor taggedClause.1.literals)
            literal.offset))
        sourcePoint)
      sourceRebasedMember
  simpa using sourceBounded.scale factor

end PositionedPeriodicCNF
end LeanTrominoes
