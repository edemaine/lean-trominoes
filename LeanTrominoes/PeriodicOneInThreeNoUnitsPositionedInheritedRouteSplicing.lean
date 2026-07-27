import LeanTrominoes.OrthogonalPolylineJoin
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedEndpoints
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Splicing unit-elimination ports to inherited routes

This file scales a source incidence route by the unit-elimination refinement
factor, translates it into a generated clause's canonical anchor gauge, and
connects its source-clause endpoint to the appropriate local boundary port.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

def inheritedSourceRouteShift
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)) :
    Cell :=
  Cell.sub
    (normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause)
    (Cell.scale gadgetScale
      (PositionedPeriodicCNF.canonicalClausePosition
        sourcePlacement sourceClause))

def inheritedSourceRoute
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceRoute : List Cell) :
    List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (inheritedSourceRouteShift
      outputPlacement sourcePlacement sourceClause generatedClause)
    (scalePolyline gadgetScale sourceRoute)

theorem inheritedSourceRoute_head?
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
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

theorem inheritedSourceRoute_getLast?
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceLiteral : PeriodicLiteral Variable)
    (generatedLiteral :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable))
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
    placement, PeriodicVariablePlacement.translation,
    gadgetScale, literalAtom, literalOffset,
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

theorem inheritedSourceRoute_orthogonal
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceRoute : List Cell)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (inheritedSourceRoute
        outputPlacement sourcePlacement sourceClause generatedClause
        sourceRoute) := by
  apply orthogonalPolyline_translate
  exact orthogonalPolyline_scale sourceOrthogonal (by decide)

def inheritedRouteSuffix
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
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

theorem inheritedRouteSuffix_valid
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceLiteral : PeriodicLiteral Variable)
    (generatedLiteral :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable))
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
  have transformedHead :
      transformed.head? = some sourcePoint :=
    inheritedSourceRoute_head?
      (placement source sourcePlacement)
      sourcePlacement sourceClause generatedClause
      sourceRoute sourceHead
  have transformedLast :
      transformed.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (placement source sourcePlacement)
            generatedClause generatedLiteral) :=
    inheritedSourceRoute_getLast?
      source sourcePlacement sourceClause generatedClause
      sourceLiteral generatedLiteral sourceRoute sourceLast
      literalAtom literalOffset
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
    ⟨joinAtEndpoint_head? (by simp [connector]),
      joinAtEndpoint_getLast?
        (by simp [connector]) transformedHead transformedLast,
      (PositionedPeriodicCNF.orthogonalDetour_orthogonal
        port sourcePoint).joinAtEndpoint
          (inheritedSourceRoute_orthogonal
            (placement source sourcePlacement)
            sourcePlacement sourceClause generatedClause
            sourceRoute sourceOrthogonal)
          (by simp) transformedHead⟩

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
