import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineInheritedEndpoints
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteSplicing

/-!
# Normalized Figure 9 local-route/exit-connector separation

The finite composed drawings and clause-exit fans are certified in a common
local coordinate system.  The selected local route and selected connector
undergo exactly the same translation into a generated clause's anchor gauge.
This file transports the finite strict-separation check to those normalized
routes.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A genuine normalized local route strictly avoids an active exit-fan
connector placed at the same source-clause origin, provided their endpoints
are distinct. -/
theorem normalizedLocalRoutes_strictlyAvoids_translatedExitConnector_of_members
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (metadata : ClauseMetadata Variable)
    (metadataLookup :
      (formulaClauseMetadata source)[clauseIndex]? = some metadata)
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (valid : data.IsValid)
    (active : data.SlotActive slot)
    (endpointsDifferent :
      (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex).getLast? ≠
        (data.translatedRoute
          (normalizedSourceClausePosition
            (composedPlacement source sourcePlacement)
            metadata.sourceClause metadata.clause)
          slot).head?) :
    RoutesStrictlyAvoidEachOther
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex)
      (data.translatedRoute
        (normalizedSourceClausePosition
          (composedPlacement source sourcePlacement)
          metadata.sourceClause metadata.clause)
        slot) := by
  rcases normalizedLocalRoutes_eq_translated_templateRoute_of_members
      source sourcePlacement sourceWidth clauseMember literalMember with
    ⟨actualMetadata, templateIndex, actualLookup, clauseEqual,
      normalizedRouteEqual⟩
  have metadataEqual : actualMetadata = metadata := by
    apply Option.some.inj
    exact actualLookup.symm.trans metadataLookup
  subst actualMetadata
  have metadataWidth : metadata.sourceClause.literals.length ≤ 3 := by
    rcases formulaClauseMetadata_lookup_valid_embedded
        source clauseMember with
      ⟨witnessMetadata, witnessLookup, _witnessClauseEqual,
        sourceClauseMember, _localClauseMember⟩
    have witnessEqual : witnessMetadata = metadata := by
      apply Option.some.inj
      exact witnessLookup.symm.trans metadataLookup
    subst witnessMetadata
    have sourceClauseMember : metadata.sourceClause ∈ source.clauses :=
      List.fst_mem_of_mem_zipIdx sourceClauseMember
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, sourceClauseMember, rfl⟩
  let origin :=
    normalizedSourceClausePosition
      (composedPlacement source sourcePlacement)
      metadata.sourceClause metadata.clause
  let templateRoute :=
    (templateDrawing metadata.sourceClause).routeAt
      ((templateDrawing metadata.sourceClause).incidenceAt templateIndex)
  have normalizedRouteEqual' :
      normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex =
        PeriodicOrthocrossing.translatePolyline origin templateRoute := by
    simpa [origin, templateRoute, normalizedSourceClausePosition]
      using normalizedRouteEqual
  have rawEndpointsDifferent :
      templateRoute.getLast? ≠ (data.route slot).head? := by
    intro rawEndpointsEqual
    apply endpointsDifferent
    rw [normalizedRouteEqual']
    simp [origin, templateRoute,
      ComposedClauseExitFanData.translatedRoute,
      PeriodicOrthocrossing.translatePolyline,
      rawEndpointsEqual]
  have finiteStrict :=
    ComposedClauseExitFanData.templateDrawing_routeAt_strictlyAvoids_route
      metadata.sourceClause metadataWidth data templateIndex slot
      valid active rawEndpointsDifferent
  have translatedStrict := finiteStrict.translatePolyline origin
  simpa [normalizedRouteEqual',
    ComposedClauseExitFanData.translatedRoute] using translatedStrict

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
