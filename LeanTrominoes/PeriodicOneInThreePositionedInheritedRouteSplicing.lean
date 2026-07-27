import LeanTrominoes.OrthogonalPolylineJoin
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.PeriodicOneInThreePositionedInheritedEndpoints
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Splicing Figure 9 source ports to inherited routes

A route inherited from the source formula lives in the source clause's
canonical anchor gauge.  Figure 9 refines all coordinates by twelve and its
local route lives in the generated clause's anchor gauge.  This file scales
and translates one source route between those gauges, then joins the
index-selected Figure 9 boundary port to the transformed route.

The generic Manhattan connector used here certifies endpoints and
orthogonality.  A later planar fan construction can replace that connector
while retaining the gauge transformation proved below.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

/-- Translation from a scaled source route's canonical gauge to one
generated Figure 9 clause's canonical gauge. -/
def inheritedSourceRouteShift
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable)) :
    Cell :=
  Cell.sub
    (normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause)
    (Cell.scale PlanarOneInThree.gadgetScale
      (PositionedPeriodicCNF.canonicalClausePosition
        sourcePlacement sourceClause))

/-- A source incidence route, refined and expressed in a generated Figure 9
clause's canonical anchor gauge. -/
def inheritedSourceRoute
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
    (sourceRoute : List Cell) :
    List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (inheritedSourceRouteShift
      outputPlacement sourcePlacement sourceClause generatedClause)
    (scalePolyline PlanarOneInThree.gadgetScale sourceRoute)

/-- The transformed source route starts at the displayed source-clause
vertex in the generated clause's anchor gauge. -/
theorem inheritedSourceRoute_head?
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
    (sourceRoute : List Cell)
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause)) :
    (inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute).head? =
        some
          (normalizedSourceClausePosition
            outputPlacement sourceClause generatedClause) := by
  simp only [inheritedSourceRoute,
    PeriodicOrthocrossing.translatePolyline,
    List.head?_map, scalePolyline_head?, sourceHead,
    Option.map_some]
  apply congrArg some
  apply Prod.ext <;>
  simp [inheritedSourceRouteShift, Cell.add, Cell.sub]

/-- The transformed route's inherited literal endpoint is exactly the
generated Figure 9 literal's canonical endpoint. -/
theorem inheritedSourceRoute_getLast?
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
    (sourceLiteral : PeriodicLiteral Variable)
    (generatedLiteral :
      PeriodicLiteral (OneInThreeVariable Variable))
    (sourceRoute : List Cell)
    (sourceLast :
      sourceRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            sourcePlacement sourceClause sourceLiteral))
    (literalAtom :
      generatedLiteral.atom = .inl sourceLiteral.atom)
    (literalOffset :
      generatedLiteral.offset = sourceLiteral.offset) :
    (inheritedSourceRoute
      (placement source sourcePlacement)
      sourcePlacement sourceClause generatedClause
      sourceRoute).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (placement source sourcePlacement)
            generatedClause generatedLiteral) := by
  simp only [inheritedSourceRoute,
    PeriodicOrthocrossing.translatePolyline,
    List.getLast?_map, scalePolyline_getLast?, sourceLast,
    Option.map_some]
  apply congrArg some
  apply Prod.ext <;>
  simp [inheritedSourceRouteShift, normalizedSourceClausePosition,
    PositionedPeriodicCNF.canonicalClausePosition,
    PositionedPeriodicCNF.canonicalLiteralPosition,
    PeriodicOneInThreePositioned.placement,
    PeriodicVariablePlacement.translation,
    PlanarOneInThree.gadgetScale,
    literalAtom, literalOffset,
    Cell.add, Cell.sub, Cell.scale]
  <;> ring

private theorem orthogonalPolyline_scale
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    {factor : Int}
    (factorPositive : 0 < factor) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (scalePolyline factor points) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline at orthogonal ⊢
  unfold scalePolyline
  apply List.isChain_map_of_isChain (Cell.scale factor)
  · intro first second aligned
    exact
      (GridSegment.isAxisAligned_scale_iff
        factorPositive (GridSegment.mk first second)).mpr aligned
  · exact orthogonal

private theorem orthogonalPolyline_translate
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (offset : Cell) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (PeriodicOrthocrossing.translatePolyline offset points) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline at orthogonal ⊢
  unfold PeriodicOrthocrossing.translatePolyline
  apply List.isChain_map_of_isChain (Cell.add offset)
  · intro first second aligned
    exact
      (GridSegment.isAxisAligned_translate
        (GridSegment.mk first second) offset).2 aligned
  · exact orthogonal

/-- Scaling and changing the anchor gauge preserve orthogonality of a source
route. -/
theorem inheritedSourceRoute_orthogonal
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
    (sourceRoute : List Cell)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (inheritedSourceRoute
        outputPlacement sourcePlacement sourceClause generatedClause
        sourceRoute) := by
  apply orthogonalPolyline_translate
  exact orthogonalPolyline_scale sourceOrthogonal (by decide)

/-- Connect a Figure 9 boundary port to the refined and gauge-transformed
source incidence route. -/
def inheritedRouteSuffix
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
    (sourceLiteralIndex : Nat)
    (sourceRoute : List Cell) :
    List Cell :=
  joinAtEndpoint
    (PositionedPeriodicCNF.orthogonalDetour
      (normalizedSourcePort outputPlacement sourceClause
        generatedClause sourceLiteralIndex)
      (normalizedSourceClausePosition outputPlacement sourceClause
        generatedClause))
    (inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute)

/-- A certified source route yields a boundary-to-variable Figure 9 suffix
with exact canonical endpoints and preserved orthogonality. -/
theorem inheritedRouteSuffix_valid
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
    (sourceLiteral : PeriodicLiteral Variable)
    (generatedLiteral :
      PeriodicLiteral (OneInThreeVariable Variable))
    (sourceLiteralIndex : Nat)
    (sourceRoute : List Cell)
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause))
    (sourceLast :
      sourceRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            sourcePlacement sourceClause sourceLiteral))
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute)
    (literalAtom :
      generatedLiteral.atom = .inl sourceLiteral.atom)
    (literalOffset :
      generatedLiteral.offset = sourceLiteral.offset) :
    (inheritedRouteSuffix
        (placement source sourcePlacement)
        sourcePlacement sourceClause generatedClause
        sourceLiteralIndex sourceRoute).head? =
        some
          (normalizedSourcePort
            (placement source sourcePlacement)
            sourceClause generatedClause sourceLiteralIndex) ∧
      (inheritedRouteSuffix
        (placement source sourcePlacement)
        sourcePlacement sourceClause generatedClause
        sourceLiteralIndex sourceRoute).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (placement source sourcePlacement)
            generatedClause generatedLiteral) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (inheritedRouteSuffix
          (placement source sourcePlacement)
          sourcePlacement sourceClause generatedClause
          sourceLiteralIndex sourceRoute) := by
  let port :=
    normalizedSourcePort
      (placement source sourcePlacement)
      sourceClause generatedClause sourceLiteralIndex
  let sourcePoint :=
    normalizedSourceClausePosition
      (placement source sourcePlacement)
      sourceClause generatedClause
  let connector :=
    PositionedPeriodicCNF.orthogonalDetour port sourcePoint
  let transformed :=
    inheritedSourceRoute
      (placement source sourcePlacement)
      sourcePlacement sourceClause generatedClause sourceRoute
  have connectorHead :
      connector.head? = some port := by
    simp [connector]
  have connectorLast :
      connector.getLast? = some sourcePoint := by
    simp [connector]
  have transformedHead :
      transformed.head? = some sourcePoint := by
    exact inheritedSourceRoute_head?
      (placement source sourcePlacement)
      sourcePlacement sourceClause generatedClause
      sourceRoute sourceHead
  have transformedLast :
      transformed.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (placement source sourcePlacement)
            generatedClause generatedLiteral) := by
    exact inheritedSourceRoute_getLast?
      source sourcePlacement sourceClause generatedClause
      sourceLiteral generatedLiteral sourceRoute sourceLast
      literalAtom literalOffset
  have connectorOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline connector :=
    PositionedPeriodicCNF.orthogonalDetour_orthogonal port sourcePoint
  have transformedOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline transformed :=
    inheritedSourceRoute_orthogonal
      (placement source sourcePlacement)
      sourcePlacement sourceClause generatedClause sourceRoute
      sourceOrthogonal
  change
    (joinAtEndpoint connector transformed).head? = some port ∧
      (joinAtEndpoint connector transformed).getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (placement source sourcePlacement)
              generatedClause generatedLiteral) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (joinAtEndpoint connector transformed)
  exact
    ⟨joinAtEndpoint_head? connectorHead,
      joinAtEndpoint_getLast?
        connectorLast transformedHead transformedLast,
      connectorOrthogonal.joinAtEndpoint
        transformedOrthogonal connectorLast transformedHead⟩

end PeriodicOneInThreePositioned
end LeanTrominoes
