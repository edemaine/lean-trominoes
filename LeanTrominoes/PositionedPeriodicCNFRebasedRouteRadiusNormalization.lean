import LeanTrominoes.PositionedPeriodicCNFRebasedRouteRadiusBounds
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalizationDrawing

/-!
# Variable-radius bounds through incidence-anchor normalization

Anchor normalization subtracts the clause anchor from every stored route
point and literal offset.  The later variable-side rebase adds back exactly
the complementary translation, so distance from the displayed physical
literal endpoint becomes distance from its variable prototype.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit

namespace PositionedPeriodicCNF

/-- Raw physical route points are within a fixed radius of the displayed
physical occurrence of their literal endpoint. -/
def IncidenceRoutesWithinPhysicalLiteralRadius
    {Variable : Type*}
    (radius : Nat)
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) : Prop :=
  ∀ clause clauseIndex,
    (clause, clauseIndex) ∈ source.clauses.zipIdx →
    ∀ literal literalIndex,
      (literal, literalIndex) ∈ clause.literals.zipIdx →
      ∀ point ∈ routes clauseIndex literalIndex,
        WithinCoordinateRadius radius
          (placement.literalPosition literal) point

/-- One-period specialization of physical literal-endpoint bounds. -/
def IncidenceRoutesWithinPhysicalLiteralPeriod
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) : Prop :=
  IncidenceRoutesWithinPhysicalLiteralRadius
    placement.period source placement routes

/-- A point bounded around a physical literal occurrence remains bounded
around the variable prototype after route normalization and the reverse
incidence rebase. -/
theorem withinCoordinateRadius_normalize_rebase
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (literal : PeriodicLiteral Variable)
    (anchor : Cell)
    {radius : Nat} {rawPoint : Cell}
    (bounded :
      WithinCoordinateRadius radius
        (placement.literalPosition literal) rawPoint) :
    WithinCoordinateRadius radius
      (placement.position literal.atom)
      (Cell.add
        (placement.translation
          (Cell.sub (0, 0)
            (literal.anchorNormalize anchor).offset))
        (Cell.sub rawPoint (placement.translation anchor))) := by
  have translated := bounded.translate
    (Cell.scale (-1) (placement.translation literal.offset))
  have centerEq :
      Cell.add
          (Cell.scale (-1) (placement.translation literal.offset))
          (placement.literalPosition literal) =
        placement.position literal.atom := by
    apply Prod.ext <;>
      simp [PeriodicVariablePlacement.literalPosition,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.scale] <;>
      ring
  have pointEq :
      Cell.add
          (Cell.scale (-1) (placement.translation literal.offset))
          rawPoint =
        Cell.add
          (placement.translation
            (Cell.sub (0, 0)
              (literal.anchorNormalize anchor).offset))
          (Cell.sub rawPoint (placement.translation anchor)) := by
    rcases anchor with ⟨anchorX, anchorY⟩
    rcases offsetEq : literal.offset with ⟨offsetX, offsetY⟩
    rcases rawPoint with ⟨pointX, pointY⟩
    apply Prod.ext <;>
      simp [PeriodicVariablePlacement.translation,
        PeriodicLiteral.anchorNormalize,
        Cell.add, Cell.sub, Cell.scale, offsetEq] <;>
      ring
  rw [centerEq, pointEq] at translated
  exact translated

/-- Physical literal-endpoint bounds become variable-prototype bounds when
the formula and route family are normalized by each clause anchor. -/
theorem IncidenceRoutesWithinPhysicalLiteralRadius.anchorNormalize
    {Variable : Type*}
    {radius : Nat}
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (bounds :
      IncidenceRoutesWithinPhysicalLiteralRadius
        radius source placement routes) :
    RebasedIncidenceRoutesWithinVariableRadius
      radius (source.anchorNormalize placement)
      placement
      (source.anchorNormalizedIncidenceRoutes placement routes) := by
  intro normalizedClause clauseIndex normalizedClauseMember
    normalizedLiteral literalIndex normalizedLiteralMember
    point pointMember
  change
    (normalizedClause, clauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨canonicalClausePosition placement clause,
          clause.literals.anchorNormalize⟩).zipIdx
    at normalizedClauseMember
  rw [List.zipIdx_map] at normalizedClauseMember
  rcases List.mem_map.mp normalizedClauseMember with
    ⟨taggedClause, taggedClauseMember, normalizedClauseEqual⟩
  have clauseIndexEqual : taggedClause.2 = clauseIndex :=
    congrArg Prod.snd normalizedClauseEqual
  have normalizedClauseValueEqual :
      normalizedClause =
        ⟨canonicalClausePosition placement taggedClause.1,
          taggedClause.1.literals.anchorNormalize⟩ :=
    (congrArg Prod.fst normalizedClauseEqual).symm
  subst clauseIndex
  subst normalizedClause
  change
    (normalizedLiteral, literalIndex) ∈
      (taggedClause.1.literals.map
        (PeriodicLiteral.anchorNormalize
          (PeriodicCNF.clauseAnchor
            taggedClause.1.literals))).zipIdx
    at normalizedLiteralMember
  rw [List.zipIdx_map] at normalizedLiteralMember
  rcases List.mem_map.mp normalizedLiteralMember with
    ⟨taggedLiteral, taggedLiteralMember,
      normalizedLiteralEqual⟩
  have literalIndexEqual : taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd normalizedLiteralEqual
  have normalizedLiteralValueEqual :
      normalizedLiteral =
        taggedLiteral.1.anchorNormalize
          (PeriodicCNF.clauseAnchor taggedClause.1.literals) :=
    (congrArg Prod.fst normalizedLiteralEqual).symm
  subst literalIndex
  subst normalizedLiteral
  have sourceClauseLookup :
      source.clauses[taggedClause.2]? = some taggedClause.1 :=
    (List.mem_zipIdx_iff_getElem?).mp taggedClauseMember
  simp only [PeriodicClause.clauseAnchor_anchorNormalize]
    at pointMember ⊢
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨normalizedPoint, normalizedPointMember, rfl⟩
  have normalizedPointMember' :
      normalizedPoint ∈
        source.anchorNormalizedIncidenceRoutes placement routes
          taggedClause.2 taggedLiteral.2 :=
    List.mem_reverse.mp normalizedPointMember
  simp only [anchorNormalizedIncidenceRoutes, sourceClauseLookup,
    normalizeIncidenceRoute] at normalizedPointMember'
  rcases List.mem_map.mp normalizedPointMember' with
    ⟨rawPoint, rawPointMember, rfl⟩
  exact withinCoordinateRadius_normalize_rebase
    placement taggedLiteral.1
      (PeriodicCNF.clauseAnchor taggedClause.1.literals)
      (bounds taggedClause.1 taggedClause.2 taggedClauseMember
        taggedLiteral.1 taggedLiteral.2 taggedLiteralMember
        rawPoint rawPointMember)

/-- One-period specialization of physical-bound anchor normalization. -/
theorem IncidenceRoutesWithinPhysicalLiteralPeriod.anchorNormalize
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (bounds :
      IncidenceRoutesWithinPhysicalLiteralPeriod
        source placement routes) :
    RebasedIncidenceRoutesWithinVariablePeriod
      (source.anchorNormalize placement)
      placement
      (source.anchorNormalizedIncidenceRoutes placement routes) := by
  exact
    IncidenceRoutesWithinPhysicalLiteralRadius.anchorNormalize bounds

end PositionedPeriodicCNF
end LeanTrominoes
