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

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
