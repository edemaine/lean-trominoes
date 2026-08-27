/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureJoin
import LeanTrominoes.OrthogonalPolylineScalingSimplicity
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineExtendedRouteDecomposition

/-!
# Separation of one Figure 9 connector from its inherited far tail

The finite connector stays within radius `73` of the source-clause gauge,
whereas the inherited tail begins at the factor-`144` refinement boundary.
Simplicity of the original source route therefore makes the two routes
strictly disjoint.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- An active translated connector is contact-free from the far tail of its
own simple source route. -/
theorem translatedConnector_strictlyAvoids_ownFarTail
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
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (first second : Cell)
    (rest : List Cell)
    (fanValid : data.IsValid)
    (slotActive : data.SlotActive slot)
    (scaledHead :
      Cell.scale 2 first =
        PositionedPeriodicCNF.canonicalClausePosition
          sourcePlacement sourceClause)
    (sourceOrthogonal :
      OrthogonalPolyline (first :: second :: rest))
    (sourceSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (first :: second :: rest)) :
    RoutesStrictlyAvoidEachOther
      (data.translatedRoute
        (normalizedSourceClausePosition
          outputPlacement sourceClause generatedClause)
        slot)
      (translatePolyline
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement sourceClause generatedClause)
        (scalePolyline composedGadgetScale
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (second :: rest))))) := by
  let origin :=
    normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause
  let shift :=
    inheritedSourceRouteShift
      outputPlacement sourcePlacement sourceClause generatedClause
  let connector := data.translatedRoute origin slot
  let farTail :=
    translatePolyline shift
      (scalePolyline composedGadgetScale
        (AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (second :: rest))))
  have connectorOrthogonal : OrthogonalPolyline connector :=
    data.translatedRoute_orthogonal origin fanValid slot slotActive
  have originEq :
      origin = Cell.add shift (Cell.scale 144 first) := by
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst scaledHead
      simp [origin, shift, inheritedSourceRouteShift,
        composedGadgetScale, PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        Cell.add, Cell.sub, Cell.scale] at coordinateEqual ⊢
      nlinarith
    · have coordinateEqual := congrArg Prod.snd scaledHead
      simp [origin, shift, inheritedSourceRouteShift,
        composedGadgetScale, PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        Cell.add, Cell.sub, Cell.scale] at coordinateEqual ⊢
      nlinarith
  have connectorBounded :
      ∀ point ∈ connector,
        WithinCoordinateRadius 73
          (Cell.add shift (Cell.scale 144 first)) point := by
    intro point pointMember
    rw [← originEq]
    exact data.translatedRoute_points_within_sourceNeighborhood
      origin fanValid slot slotActive pointMember
  exact
    strictlyAvoids_translatedScaledDoubledSubdividedTail_of_radius
      shift 73 (by norm_num) sourceOrthogonal sourceSimple
      connectorOrthogonal connectorBounded

/-- The radial extension joined to the inherited far tail is a transformed
tail of the refined simple source route, and is therefore simple. -/
theorem radialJoinFarTail_isSimple
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
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (first second : Cell)
    (rest : List Cell)
    (firstUnit : AxisDirection.IsUnitAxisStep first second)
    (scaledHead :
      Cell.scale 2 first =
        PositionedPeriodicCNF.canonicalClausePosition
          sourcePlacement sourceClause)
    (directionEq :
      data.direction slot = AxisDirection.between first second)
    (sourceOrthogonal :
      OrthogonalPolyline (first :: second :: rest))
    (sourceSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (first :: second :: rest)) :
    LocalIncidenceDrawing.RouteIsSimple
      (joinAtEndpoint
        (data.translatedRadialExtension
          (normalizedSourceClausePosition
            outputPlacement sourceClause generatedClause)
          slot)
        (translatePolyline
          (inheritedSourceRouteShift
            outputPlacement sourcePlacement sourceClause generatedClause)
          (scalePolyline composedGadgetScale
            (AxisDirection.unitSubdividePolyline
              (scalePolyline 2 (second :: rest)))))) := by
  let sourceRoute := first :: second :: rest
  let doubled := scalePolyline 2 sourceRoute
  let refined := AxisDirection.unitSubdividePolyline doubled
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause refined
  have doubledNonempty : doubled ≠ [] := by
    simp [doubled, sourceRoute, scalePolyline]
  have doubledOrthogonal : OrthogonalPolyline doubled := by
    exact sourceOrthogonal.scalePolyline (by norm_num)
  have doubledSimple :
      LocalIncidenceDrawing.RouteIsSimple doubled := by
    exact sourceSimple.scalePolyline (by norm_num)
  have refinedSimple :
      LocalIncidenceDrawing.RouteIsSimple refined := by
    have normalizedSimple :=
      AxisDirection.normalizeOrthogonalPolyline_isSimple
        doubledNonempty doubledOrthogonal
    rw [AxisDirection.normalizeOrthogonalPolyline_eq_unitSubdividePolyline_of_simple
      doubledNonempty doubledOrthogonal doubledSimple] at normalizedSimple
    exact normalizedSimple
  have transformedSimple :
      LocalIncidenceDrawing.RouteIsSimple transformed := by
    unfold transformed inheritedSourceRoute translatePolyline
    exact routeIsSimple_translate
      (refinedSimple.scalePolyline (by
        norm_num [composedGadgetScale, PlanarOneInThree.gadgetScale,
          PeriodicOneInThreeNoUnitsPositioned.gadgetScale]))
      (inheritedSourceRouteShift
        outputPlacement sourcePlacement sourceClause generatedClause)
  have transformedTailSimple :
      LocalIncidenceDrawing.RouteIsSimple transformed.tail :=
    transformedSimple.tail
  have tailEq := inheritedSourceRoute_tail_eq_radial_join_farTail
    outputPlacement sourcePlacement sourceClause generatedClause
    data slot first second rest firstUnit scaledHead directionEq
  change LocalIncidenceDrawing.RouteIsSimple
    (joinAtEndpoint
      (translatePolyline
        (normalizedSourceClausePosition
          outputPlacement sourceClause generatedClause)
        [ComposedClauseExitFanData.sourceExit (data.direction slot),
          ComposedClauseExitFanData.outerSourceExit
            (data.direction slot)])
      (translatePolyline
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement sourceClause generatedClause)
        (scalePolyline composedGadgetScale
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (second :: rest))))))
  rw [← tailEq]
  simpa [transformed, refined, doubled, sourceRoute] using
    transformedTailSimple

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
