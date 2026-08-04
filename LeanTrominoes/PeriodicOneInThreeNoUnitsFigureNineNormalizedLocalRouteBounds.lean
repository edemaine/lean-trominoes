import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalRouteBounds
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineInheritedEndpoints

/-!
# Bounds for anchor-normalized composed Figure 9 local routes

Physical Figure 9 routes lie in a radius-36 neighborhood at a fixed offset
from their refined source-clause position.  Subtracting the generated clause
anchor translates both the route and that center into the canonical gauge.
This is the form used by relative splice separation.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PeriodicEightOccurrenceSplit

/-- The physical source-clause position expressed in one generated clause's
anchor gauge, before the combined factor-72 refinement. -/
def localRouteSourceGaugeCenter
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))) : Cell :=
  Cell.sub sourceClause.position
    (sourcePlacement.translation
      (PeriodicCNF.clauseAnchor generatedClause.literals))

/-- Anchor normalization commutes with the combined refinement: the local
route's source center is factor 72 times its unrefined source-gauge center. -/
theorem normalizedSourceClausePosition_eq_scale_sourceGaugeCenter
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))) :
    normalizedSourceClausePosition
        (composedPlacement source sourcePlacement)
        sourceClause generatedClause =
      Cell.scale composedGadgetScale
        (localRouteSourceGaugeCenter
          sourcePlacement sourceClause generatedClause) := by
  apply Prod.ext <;>
    simp [normalizedSourceClausePosition,
      localRouteSourceGaugeCenter, composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      PeriodicVariablePlacement.translation,
      composedGadgetScale, PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      Cell.sub, Cell.scale] <;>
    ring

/-- Translating a normalized source center by an output period translates
its source-gauge center before factor-72 refinement. -/
theorem translated_normalizedSourceClausePosition_eq_scale_sourceGaugeCenter
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (relativeTranslate : Cell) :
    Cell.add
        ((composedPlacement source sourcePlacement).translation
          relativeTranslate)
        (normalizedSourceClausePosition
          (composedPlacement source sourcePlacement)
          sourceClause generatedClause) =
      Cell.scale composedGadgetScale
        (Cell.add
          (sourcePlacement.translation relativeTranslate)
          (localRouteSourceGaugeCenter
            sourcePlacement sourceClause generatedClause)) := by
  rw [normalizedSourceClausePosition_eq_scale_sourceGaugeCenter]
  apply Prod.ext <;>
    simp [composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      PeriodicVariablePlacement.translation,
      composedGadgetScale, PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      Cell.add, Cell.scale] <;>
    ring

/-- Every genuine normalized local route stays within radius 36 of its
offset source-clause center in the generated clause's canonical anchor
gauge. -/
theorem normalizedLocalRoutes_points_within_sourceNeighborhood_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ metadata : ClauseMetadata Variable,
      (formulaClauseMetadata source)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
        (metadata.sourceClause, metadata.sourceClauseIndex) ∈
          source.clauses.zipIdx ∧
        ∀ point ∈
            normalizedLocalRoutes source sourcePlacement
              clauseIndex literalIndex,
          WithinCoordinateRadius 36
            (Cell.add
              (normalizedSourceClausePosition
                (composedPlacement source sourcePlacement)
                metadata.sourceClause clause)
              localRouteNeighborhoodOffset) point := by
  rcases localRoutes_points_within_sourceNeighborhood_of_members
      source sourceWidth clauseMember literalMember with
    ⟨metadata, metadataLookup, metadataClause,
      sourceClauseMember, physicalBounded⟩
  refine
    ⟨metadata, metadataLookup, metadataClause,
      sourceClauseMember, ?_⟩
  intro point pointMember
  subst clause
  simp only [normalizedLocalRoutes, metadataLookup] at pointMember
  unfold PositionedPeriodicCNF.normalizeIncidenceRoute at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨physicalPoint, physicalPointMember, rfl⟩
  let anchor :=
    (composedPlacement source sourcePlacement).translation
      (PeriodicCNF.clauseAnchor metadata.clause.literals)
  have translated :=
    (physicalBounded physicalPoint physicalPointMember).translate
      (Cell.scale (-1) anchor)
  simpa [normalizedSourceClausePosition,
    anchor, Cell.add, Cell.sub, Cell.scale,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using translated

/-- Source-gauge form of the normalized radius-36 bound. -/
theorem normalizedLocalRoutes_points_within_sourceGaugeNeighborhood_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ metadata : ClauseMetadata Variable,
      (formulaClauseMetadata source)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
        (metadata.sourceClause, metadata.sourceClauseIndex) ∈
          source.clauses.zipIdx ∧
        ∀ point ∈
            normalizedLocalRoutes source sourcePlacement
              clauseIndex literalIndex,
          WithinCoordinateRadius 36
            (Cell.add
              (Cell.scale composedGadgetScale
                (localRouteSourceGaugeCenter
                  sourcePlacement metadata.sourceClause clause))
              localRouteNeighborhoodOffset) point := by
  rcases normalizedLocalRoutes_points_within_sourceNeighborhood_of_members
      source sourcePlacement sourceWidth clauseMember literalMember with
    ⟨metadata, metadataLookup, metadataClause,
      sourceClauseMember, bounded⟩
  refine
    ⟨metadata, metadataLookup, metadataClause,
      sourceClauseMember, ?_⟩
  intro point pointMember
  simpa [normalizedSourceClausePosition_eq_scale_sourceGaugeCenter]
    using bounded point pointMember

/-- Every genuine normalized local route lies in the coarser radius-72
square centered directly at its factor-72 source-clause gauge.  The extra
room absorbs the fixed `(36, 32)` offset of the tighter local template
bound. -/
theorem normalizedLocalRoutes_points_within_sourceGaugeRadius72_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ metadata : ClauseMetadata Variable,
      (formulaClauseMetadata source)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
        (metadata.sourceClause, metadata.sourceClauseIndex) ∈
          source.clauses.zipIdx ∧
        ∀ point ∈
            normalizedLocalRoutes source sourcePlacement
              clauseIndex literalIndex,
          WithinCoordinateRadius 72
            (Cell.scale composedGadgetScale
              (localRouteSourceGaugeCenter
                sourcePlacement metadata.sourceClause clause)) point := by
  rcases normalizedLocalRoutes_points_within_sourceGaugeNeighborhood_of_members
      source sourcePlacement sourceWidth clauseMember literalMember with
    ⟨metadata, metadataLookup, metadataClause,
      sourceClauseMember, bounded⟩
  refine
    ⟨metadata, metadataLookup, metadataClause,
      sourceClauseMember, ?_⟩
  intro point pointMember
  let center :=
    Cell.scale composedGadgetScale
      (localRouteSourceGaugeCenter
        sourcePlacement metadata.sourceClause clause)
  have tight := bounded point pointMember
  change
    WithinCoordinateRadius 36
      (Cell.add center localRouteNeighborhoodOffset) point at tight
  rcases tight with ⟨horizontal, vertical⟩
  constructor
  · have decomposition :
        point.1 - center.1 =
          (point.1 -
              (Cell.add center localRouteNeighborhoodOffset).1) + 36 := by
      simp [localRouteNeighborhoodOffset, Cell.add]
      ring
    rw [decomposition]
    exact
      (Int.natAbs_add_le _ _).trans
        (by
          simpa using Nat.add_le_add horizontal
            (show (36 : Int).natAbs ≤ 36 by norm_num))
  · have decomposition :
        point.2 - center.2 =
          (point.2 -
              (Cell.add center localRouteNeighborhoodOffset).2) + 32 := by
      simp [localRouteNeighborhoodOffset, Cell.add]
      ring
    rw [decomposition]
    exact
      (Int.natAbs_add_le _ _).trans
        (by
          have sumBound := Nat.add_le_add vertical
            (show (32 : Int).natAbs ≤ 32 by norm_num)
          omega)

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
