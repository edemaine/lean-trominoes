import LeanTrominoes.OrthogonalPolylineHeadReplacement
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineInheritedEndpoints
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Directly splicing composed ports to original source routes

The composed local certificate already contains both Figure 9 and unit
elimination, so a twice-inherited incidence should attach directly to the
original source route.  This file scales that route by the combined factor
`72`, changes from the source clause's anchor gauge to the final clause's
anchor gauge, and replaces its obsolete source-clause head by a connector
from the certified composed boundary port to the transformed first exit.

This generic connector certifies exact endpoints and orthogonality.  Its
continuous noncrossing geometry is a later global obligation.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

/-- Translation from a scaled original source route's canonical gauge to a
final generated clause's canonical gauge. -/
def inheritedSourceRouteShift
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))) :
    Cell :=
  Cell.sub
    (normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause)
    (Cell.scale composedGadgetScale
      (PositionedPeriodicCNF.canonicalClausePosition
        sourcePlacement sourceClause))

/-- For the actual twice-refined placement, the inherited-route shift is a
whole output-period translation: it is exactly the difference between the
original source-clause anchor and the final generated-clause anchor. -/
theorem inheritedSourceRouteShift_composedPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))) :
    inheritedSourceRouteShift
        (composedPlacement source sourcePlacement)
        sourcePlacement sourceClause generatedClause =
      (composedPlacement source sourcePlacement).translation
        (Cell.sub
          (PeriodicCNF.clauseAnchor sourceClause.literals)
          (PeriodicCNF.clauseAnchor generatedClause.literals)) := by
  apply Prod.ext <;>
    simp [inheritedSourceRouteShift,
      normalizedSourceClausePosition,
      PositionedPeriodicCNF.canonicalClausePosition,
      composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      PeriodicVariablePlacement.translation,
      composedGadgetScale, PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      Cell.sub, Cell.scale] <;>
    ring

/-- Whole-period gauge used to express an inherited source route in one
generated clause's canonical representative. -/
def inheritedSourceRouteGauge
    {Variable : Type*}
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))) : Cell :=
  Cell.sub
    (PeriodicCNF.clauseAnchor sourceClause.literals)
    (PeriodicCNF.clauseAnchor generatedClause.literals)

/-- Source-level relative translation corresponding to a comparison of two
generated-clause gauges at the requested output translation. -/
def inheritedSourceRelativeTranslate
    {Variable : Type*}
    (firstSourceClause secondSourceClause :
      PositionedPeriodicClause Variable)
    (firstGeneratedClause secondGeneratedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (relativeTranslate : Cell) : Cell :=
  Cell.sub
    (Cell.add relativeTranslate
      (inheritedSourceRouteGauge
        secondSourceClause secondGeneratedClause))
    (inheritedSourceRouteGauge
      firstSourceClause firstGeneratedClause)

/-- An original source incidence route, refined by the combined factor and
expressed in a final generated clause's canonical anchor gauge. -/
def inheritedSourceRoute
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceRoute : List Cell) :
    List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (inheritedSourceRouteShift
      outputPlacement sourcePlacement sourceClause generatedClause)
    (scalePolyline composedGadgetScale sourceRoute)

/-- The transformed source route begins at the displayed original
source-clause vertex in the final clause's gauge. -/
theorem inheritedSourceRoute_head?
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
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

/-- The transformed route's original-variable endpoint is exactly the
twice-inherited final literal's canonical endpoint. -/
theorem inheritedSourceRoute_getLast?
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceLiteral : PeriodicLiteral Variable)
    (generatedLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceRoute : List Cell)
    (sourceLast :
      sourceRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            sourcePlacement sourceClause sourceLiteral))
    (literalAtom :
      generatedLiteral.atom =
        .inl (.inl sourceLiteral.atom))
    (literalOffset :
      generatedLiteral.offset = sourceLiteral.offset) :
    (inheritedSourceRoute
      (composedPlacement source sourcePlacement)
      sourcePlacement sourceClause generatedClause
      sourceRoute).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (composedPlacement source sourcePlacement)
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
    composedPlacement,
    PeriodicOneInThreeNoUnitsPositioned.placement,
    PeriodicOneInThreePositioned.placement,
    PeriodicVariablePlacement.translation,
    composedGadgetScale,
    PlanarOneInThree.gadgetScale,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
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

/-- Combined scaling and anchor-gauge translation preserve
orthogonality. -/
theorem inheritedSourceRoute_orthogonal
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceRoute : List Cell)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (inheritedSourceRoute
        outputPlacement sourcePlacement sourceClause generatedClause
        sourceRoute) := by
  apply orthogonalPolyline_translate
  exact orthogonalPolyline_scale sourceOrthogonal
    (by
      simp [composedGadgetScale,
        PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale])

/-- Scaling and changing the gauge carry a source route's first exit to its
correspondingly transformed point. -/
theorem inheritedSourceRoute_tail_head?
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceRoute : List Cell)
    (sourceExit : Cell)
    (sourceTailHead :
      sourceRoute.tail.head? = some sourceExit) :
    (inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute).tail.head? =
        some
          (Cell.add
            (inheritedSourceRouteShift
              outputPlacement sourcePlacement sourceClause
              generatedClause)
            (Cell.scale composedGadgetScale sourceExit)) := by
  simpa [inheritedSourceRoute,
    PeriodicOrthocrossing.translatePolyline,
    scalePolyline] using
    List.tail_head?_map
      (Cell.add
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement sourceClause generatedClause))
      (List.tail_head?_map
        (Cell.scale composedGadgetScale) sourceTailHead)

/-- Relative separation of two source routes survives their common
factor-`72` refinement and their two possibly different output gauges.  The
single displayed equality is the affine bookkeeping needed to identify the
translated second transformed route with the transformed source comparison.
-/
theorem inheritedSourceRoutes_relative_avoidEachOther_of_source
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (firstSourceClause secondSourceClause :
      PositionedPeriodicClause Variable)
    (firstGeneratedClause secondGeneratedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (firstSourceRoute secondSourceRoute : List Cell)
    (sourceOffset outputOffset : Cell)
    (sourceAvoids :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        firstSourceRoute
        (secondSourceRoute.map (Cell.add sourceOffset)))
    (offsetsAgree :
      Cell.add
          (inheritedSourceRouteShift
            outputPlacement sourcePlacement firstSourceClause
            firstGeneratedClause)
          (Cell.scale composedGadgetScale sourceOffset) =
        Cell.add outputOffset
          (inheritedSourceRouteShift
            outputPlacement sourcePlacement secondSourceClause
            secondGeneratedClause)) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (inheritedSourceRoute
        outputPlacement sourcePlacement firstSourceClause
        firstGeneratedClause firstSourceRoute)
      ((inheritedSourceRoute
          outputPlacement sourcePlacement secondSourceClause
          secondGeneratedClause secondSourceRoute).map
        (Cell.add outputOffset)) := by
  have factorPositive : 0 < composedGadgetScale := by
    simp [composedGadgetScale, PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale]
  have scaled := sourceAvoids.scalePolyline factorPositive
  have translated :=
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_translate
      scaled
      (inheritedSourceRouteShift
        outputPlacement sourcePlacement firstSourceClause
        firstGeneratedClause)
  have secondRouteEq :
      PeriodicOrthocrossing.translatePolyline
          (inheritedSourceRouteShift
            outputPlacement sourcePlacement firstSourceClause
            firstGeneratedClause)
          (scalePolyline composedGadgetScale
            (secondSourceRoute.map (Cell.add sourceOffset))) =
        (inheritedSourceRoute
            outputPlacement sourcePlacement secondSourceClause
            secondGeneratedClause secondSourceRoute).map
          (Cell.add outputOffset) := by
    simp only [inheritedSourceRoute,
      PeriodicOrthocrossing.translatePolyline, scalePolyline,
      List.map_map]
    apply List.map_congr_left
    intro point _pointMember
    apply Prod.ext <;>
      simp [Cell.add, Cell.scale, composedGadgetScale,
        PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale]
        at offsetsAgree ⊢ <;>
      omega
  change
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (PeriodicOrthocrossing.translatePolyline
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement firstSourceClause
          firstGeneratedClause)
        (scalePolyline composedGadgetScale firstSourceRoute))
      (PeriodicOrthocrossing.translatePolyline
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement firstSourceClause
          firstGeneratedClause)
        (scalePolyline composedGadgetScale
          (secondSourceRoute.map (Cell.add sourceOffset)))) at translated
  rw [secondRouteEq] at translated
  simpa [inheritedSourceRoute] using translated

/-- The concrete twice-refined placement automatically satisfies the affine
side condition of `inheritedSourceRoutes_relative_avoidEachOther_of_source`.
Thus transformed inherited cores are relatively separated whenever their
source routes are separated at the anchor-adjusted source translation. -/
theorem inheritedSourceRoutes_relative_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (firstSourceClause secondSourceClause :
      PositionedPeriodicClause Variable)
    (firstGeneratedClause secondGeneratedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (firstSourceRoute secondSourceRoute : List Cell)
    (relativeTranslate : Cell)
    (sourceAvoids :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        firstSourceRoute
        (secondSourceRoute.map
          (Cell.add
            (sourcePlacement.translation
              (inheritedSourceRelativeTranslate
                firstSourceClause secondSourceClause
                firstGeneratedClause secondGeneratedClause
                relativeTranslate))))) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (inheritedSourceRoute
        (composedPlacement source sourcePlacement)
        sourcePlacement firstSourceClause firstGeneratedClause
        firstSourceRoute)
      ((inheritedSourceRoute
          (composedPlacement source sourcePlacement)
          sourcePlacement secondSourceClause secondGeneratedClause
          secondSourceRoute).map
        (Cell.add
          ((composedPlacement source sourcePlacement).translation
            relativeTranslate))) := by
  apply inheritedSourceRoutes_relative_avoidEachOther_of_source
    (sourceOffset :=
      sourcePlacement.translation
        (inheritedSourceRelativeTranslate
          firstSourceClause secondSourceClause
          firstGeneratedClause secondGeneratedClause
          relativeTranslate))
    (outputOffset :=
      (composedPlacement source sourcePlacement).translation
        relativeTranslate)
    <;> try assumption
  rw [inheritedSourceRouteShift_composedPlacement,
    inheritedSourceRouteShift_composedPlacement]
  apply Prod.ext <;>
    simp [inheritedSourceRelativeTranslate,
      inheritedSourceRouteGauge,
      composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      PeriodicVariablePlacement.translation,
      composedGadgetScale,
      PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- Attach a composed boundary port directly to the transformed first exit
of an original source route. -/
def inheritedRouteSuffix
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceLiteralIndex : Nat)
    (sourceRoute : List Cell) :
    List Cell :=
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute
  replacePolylineHead
    (PositionedPeriodicCNF.orthogonalDetour
      (normalizedSourcePort outputPlacement sourceClause
        generatedClause sourceLiteralIndex)
      (polylineFirstExit transformed))
    transformed

/-- A certified original source route yields a composed
boundary-to-variable suffix with exact canonical endpoints and preserved
orthogonality. -/
theorem inheritedRouteSuffix_valid
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceLiteral : PeriodicLiteral Variable)
    (generatedLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
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
    (sourceTailNonempty :
      ∃ sourceExit,
        sourceRoute.tail.head? = some sourceExit)
    (literalAtom :
      generatedLiteral.atom =
        .inl (.inl sourceLiteral.atom))
    (literalOffset :
      generatedLiteral.offset = sourceLiteral.offset) :
    (inheritedRouteSuffix
        (composedPlacement source sourcePlacement)
        sourcePlacement sourceClause generatedClause
        sourceLiteralIndex sourceRoute).head? =
        some
          (normalizedSourcePort
            (composedPlacement source sourcePlacement)
            sourceClause generatedClause sourceLiteralIndex) ∧
      (inheritedRouteSuffix
        (composedPlacement source sourcePlacement)
        sourcePlacement sourceClause generatedClause
        sourceLiteralIndex sourceRoute).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (composedPlacement source sourcePlacement)
            generatedClause generatedLiteral) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (inheritedRouteSuffix
          (composedPlacement source sourcePlacement)
          sourcePlacement sourceClause generatedClause
          sourceLiteralIndex sourceRoute) := by
  let port :=
    normalizedSourcePort
      (composedPlacement source sourcePlacement)
      sourceClause generatedClause sourceLiteralIndex
  let transformed : List Cell :=
    inheritedSourceRoute
      (composedPlacement source sourcePlacement)
      sourcePlacement sourceClause generatedClause sourceRoute
  have _transformedHead :
      transformed.head? =
        some
          (normalizedSourceClausePosition
            (composedPlacement source sourcePlacement)
            sourceClause generatedClause) :=
    inheritedSourceRoute_head?
      (composedPlacement source sourcePlacement)
      sourcePlacement sourceClause generatedClause
      sourceRoute sourceHead
  have transformedTailNonempty :
      ∃ transformedExit,
        transformed.tail.head? = some transformedExit := by
    rcases sourceTailNonempty with
      ⟨sourceExit, sourceTailHead⟩
    exact
      ⟨Cell.add
          (inheritedSourceRouteShift
            (composedPlacement source sourcePlacement)
            sourcePlacement sourceClause generatedClause)
          (Cell.scale composedGadgetScale sourceExit),
        inheritedSourceRoute_tail_head?
          (composedPlacement source sourcePlacement)
          sourcePlacement sourceClause generatedClause
          sourceRoute sourceExit sourceTailHead⟩
  have transformedTailHead :
      transformed.tail.head? =
        some (polylineFirstExit transformed) :=
    polylineFirstExit_spec transformedTailNonempty
  let connector :=
    PositionedPeriodicCNF.orthogonalDetour
      port (polylineFirstExit transformed)
  have transformedLast :
      transformed.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (composedPlacement source sourcePlacement)
            generatedClause generatedLiteral) :=
    inheritedSourceRoute_getLast?
      source sourcePlacement sourceClause generatedClause
      sourceLiteral generatedLiteral sourceRoute sourceLast
      literalAtom literalOffset
  change
    (replacePolylineHead connector transformed).head? =
        some port ∧
      (replacePolylineHead connector transformed).getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (composedPlacement source sourcePlacement)
              generatedClause generatedLiteral) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (replacePolylineHead connector transformed)
  exact
    ⟨replacePolylineHead_head? (by simp [connector]),
      replacePolylineHead_getLast?
        (by simp [connector]) transformedTailHead transformedLast,
      (PositionedPeriodicCNF.orthogonalDetour_orthogonal
        port (polylineFirstExit transformed)).replaceHead
          (inheritedSourceRoute_orthogonal
            (composedPlacement source sourcePlacement)
            sourcePlacement sourceClause generatedClause
            sourceRoute sourceOrthogonal)
          (by simp) transformedTailHead⟩

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
