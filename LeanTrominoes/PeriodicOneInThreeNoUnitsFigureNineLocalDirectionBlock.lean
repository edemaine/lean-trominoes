/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalDirectionProfile
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalExtendedDirectionTranslation

/-! # Finite normalized direction blocks for Figure 9 local routes -/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open Gadget
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicOrthocrossing

/-- Every genuine normalized local route is emitted by one finite local
direction query. -/
theorem normalizedLocalRoutes_directionBlock_of_members
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause.literals ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ query : LocalDirectionQuery,
      unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (normalizedLocalRoutes source sourcePlacement
              clauseIndex literalIndex)) =
        normalizedLocalDirectionBlock query := by
  rcases normalizedLocalRoutes_eq_translated_profileRoute_of_members
      source sourcePlacement sourceWidth sourceClausesNonempty
      clauseMember literalMember with
    ⟨profile, templateIndex, origin, localRouteEq⟩
  let localRoute :=
    normalizedLocalRoutes source sourcePlacement clauseIndex literalIndex
  have endpoints := normalizedLocalRoutes_endpoints_of_members
    source sourcePlacement sourceWidth sourceDistinct
    clauseMember literalMember
  have localRouteNonempty : localRoute ≠ [] := by
    intro empty
    have := endpoints.1
    simp [localRoute, empty] at this
  have localRouteOrthogonal : OrthogonalPolyline localRoute :=
    normalizedLocalRoutes_orthogonal_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember
  refine ⟨⟨profile, templateIndex⟩, ?_⟩
  exact normalizedTranslatedLocalRoute_directionWord
    profile templateIndex origin localRoute localRouteEq
    localRouteNonempty localRouteOrthogonal

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
