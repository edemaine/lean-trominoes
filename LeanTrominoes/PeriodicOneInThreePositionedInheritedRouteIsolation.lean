/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePositionedInheritedRouteSplicing
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionJoin
import LeanTrominoes.PositionedPeriodicCNFOrthogonalDetourTranslation
import LeanTrominoes.EmbeddedCNFIncidenceDrawingMapPoints

/-!
# Endpoint isolation for inherited Figure 9 route suffixes

Figure 9 refines an inherited source route by a factor of twelve and attaches
a short local boundary connector at its clause end.  Positive refinement and
translation preserve simplicity.  A finite calculation for the three Figure
9 ports shows that the connector contains no other point of the refined source
lattice, so it cannot revisit the transformed variable endpoint of a
nondegenerate simple source route.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

private theorem routeIsSimple_scalePolyline
    {route : List Cell}
    {factor : Int} (factorPositive : 0 < factor)
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    LocalIncidenceDrawing.RouteIsSimple
      (scalePolyline factor route) := by
  let geometry :
      PlanarThreeSAT.GridDrawingMap (Cell.scale factor) :=
    { injective := Cell.scale_injective factorPositive.ne'
      isAxisAligned := fun {segment} aligned => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          (GridSegment.isAxisAligned_scale_iff
            factorPositive segment).mpr aligned
      interiorContains_iff := fun {segment point} => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          GridSegment.interiorContains_scale_iff
            factorPositive segment point
      interiorsMeet_iff := fun {first second} => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          GridSegment.interiorsMeet_scale_iff
            factorPositive first second }
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_mapPoints
      geometry simple

/-- Refinement and anchor-gauge translation preserve continuous simplicity
of an inherited source route. -/
theorem inheritedSourceRoute_isSimple
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
    (sourceRoute : List Cell)
    (sourceSimple :
      LocalIncidenceDrawing.RouteIsSimple sourceRoute) :
    LocalIncidenceDrawing.RouteIsSimple
      (inheritedSourceRoute
        outputPlacement sourcePlacement sourceClause generatedClause
        sourceRoute) := by
  unfold inheritedSourceRoute PeriodicOrthocrossing.translatePolyline
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      (routeIsSimple_scalePolyline (by decide) sourceSimple)
      (inheritedSourceRouteShift
        outputPlacement sourcePlacement sourceClause generatedClause)

private theorem endpoints_ne_of_simple
    {route : List Cell} {first last : Cell}
    (length : 2 ≤ route.length)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (head : route.head? = some first)
    (getLast : route.getLast? = some last) :
    first ≠ last := by
  cases route with
  | nil => simp at length
  | cons point rest =>
      cases rest with
      | nil => simp at length
      | cons next tail =>
          have pointEqual : point = first :=
            Option.some.inj head
          subst point
          have lastLookup :
              (next :: tail).getLast? = some last := by
            simpa using getLast
          have lastMember : last ∈ next :: tail :=
            List.mem_of_mem_getLast? (by simp [lastLookup])
          intro equal
          subst last
          exact (List.nodup_cons.mp simple.1).1 lastMember

/-- Among points of the scale-twelve source lattice, a local Figure 9
boundary connector contains only its target source-clause point. -/
theorem sourceConnector_scaledGridPoint_eq_zero
    (literalIndex : Nat) (point : Cell)
    (member :
      Cell.scale PlanarOneInThree.gadgetScale point ∈
        AxisDirection.unitSubdividePolyline
          (PositionedPeriodicCNF.orthogonalDetour
            (PlanarOneInThreePositioned.sourceLocalPosition literalIndex)
            (0, 0))) :
    point = (0, 0) := by
  rcases point with ⟨x, y⟩
  rcases literalIndex with _ | literalIndex
  · norm_num [PlanarOneInThree.gadgetScale,
      PlanarOneInThreePositioned.sourceLocalPosition,
      PositionedPeriodicCNF.orthogonalDetour,
      PositionedPeriodicCNF.freshDetourCoordinate,
      AxisDirection.unitSubdividePolyline,
      AxisDirection.unitSegmentPoints,
      AxisDirection.segmentLength,
      AxisDirection.between, AxisDirection.step,
      Cell.add, Cell.scale, LeanTrominoes.joinAtEndpoint,
      List.range_succ] at member ⊢
    omega
  · rcases literalIndex with _ | literalIndex
    · norm_num [PlanarOneInThree.gadgetScale,
        PlanarOneInThreePositioned.sourceLocalPosition,
        PositionedPeriodicCNF.orthogonalDetour,
        PositionedPeriodicCNF.freshDetourCoordinate,
        AxisDirection.unitSubdividePolyline,
        AxisDirection.unitSegmentPoints,
        AxisDirection.segmentLength,
        AxisDirection.between, AxisDirection.step,
        Cell.add, Cell.scale, LeanTrominoes.joinAtEndpoint,
        List.range_succ] at member ⊢
      omega
    · norm_num [PlanarOneInThree.gadgetScale,
        PlanarOneInThreePositioned.sourceLocalPosition,
        PositionedPeriodicCNF.orthogonalDetour,
        PositionedPeriodicCNF.freshDetourCoordinate,
        AxisDirection.unitSubdividePolyline,
        AxisDirection.unitSegmentPoints,
        AxisDirection.segmentLength,
        AxisDirection.between, AxisDirection.step,
        Cell.add, Cell.scale, LeanTrominoes.joinAtEndpoint,
        List.range_succ] at member ⊢
      omega

/-- Attaching the local Figure 9 boundary connector preserves isolation of
the transformed source route's final endpoint after unit subdivision. -/
theorem inheritedRouteSuffix_lastNotInDropLast
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
    (sourceLiteralIndex : Nat)
    (sourceRoute : List Cell)
    {sourceLast : Cell}
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause))
    (sourceGetLast : sourceRoute.getLast? = some sourceLast)
    (sourceLength : 2 ≤ sourceRoute.length)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute)
    (sourceSimple :
      LocalIncidenceDrawing.RouteIsSimple sourceRoute) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (inheritedRouteSuffix
          outputPlacement sourcePlacement sourceClause generatedClause
          sourceLiteralIndex sourceRoute)) := by
  let shift :=
    inheritedSourceRouteShift
      outputPlacement sourcePlacement sourceClause generatedClause
  let sourceFirst :=
    PositionedPeriodicCNF.canonicalClausePosition
      sourcePlacement sourceClause
  let sourcePoint :=
    normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause
  let port :=
    normalizedSourcePort
      outputPlacement sourceClause generatedClause sourceLiteralIndex
  let connector :=
    PositionedPeriodicCNF.orthogonalDetour port sourcePoint
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause sourceRoute
  let transformedLast :=
    Cell.add shift
      (Cell.scale PlanarOneInThree.gadgetScale sourceLast)
  have sourceEndpointsDifferent : sourceFirst ≠ sourceLast :=
    endpoints_ne_of_simple sourceLength sourceSimple
      sourceHead sourceGetLast
  have sourcePointEqual :
      sourcePoint =
        Cell.add shift
          (Cell.scale PlanarOneInThree.gadgetScale sourceFirst) := by
    simp only [sourcePoint, shift, sourceFirst,
      inheritedSourceRouteShift]
    apply Prod.ext <;>
      simp [normalizedSourceClausePosition,
        PositionedPeriodicCNF.canonicalClausePosition,
        Cell.add, Cell.sub, Cell.scale]
  have portEqual :
      port = Cell.add sourcePoint
        (PlanarOneInThreePositioned.sourceLocalPosition sourceLiteralIndex) :=
    rfl
  have connectorEqual :
      connector =
        (PositionedPeriodicCNF.orthogonalDetour
          (PlanarOneInThreePositioned.sourceLocalPosition sourceLiteralIndex)
          (0, 0)).map (Cell.add sourcePoint) := by
    rw [← PositionedPeriodicCNF.orthogonalDetour_add_left]
    simp [connector, portEqual, Cell.add]
  have transformedHead : transformed.head? = some sourcePoint := by
    exact inheritedSourceRoute_head?
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute sourceHead
  have transformedGetLast :
      transformed.getLast? = some transformedLast := by
    simp [transformed, transformedLast, shift, inheritedSourceRoute,
      PeriodicOrthocrossing.translatePolyline, sourceGetLast]
  have transformedLength : 2 ≤ transformed.length := by
    change
      2 ≤
        (PeriodicOrthocrossing.translatePolyline shift
          (scalePolyline PlanarOneInThree.gadgetScale sourceRoute)).length
    simpa only [PeriodicOrthocrossing.translatePolyline,
      List.length_map, scalePolyline] using sourceLength
  have connectorHead : connector.head? = some port := by
    simp [connector]
  have connectorGetLast : connector.getLast? = some sourcePoint := by
    simp [connector]
  have connectorNonempty : connector ≠ [] := by
    intro empty
    simp [empty] at connectorHead
  have connectorOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline connector :=
    PositionedPeriodicCNF.orthogonalDetour_orthogonal port sourcePoint
  have transformedOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline transformed :=
    inheritedSourceRoute_orthogonal
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute sourceOrthogonal
  have transformedSimple :
      LocalIncidenceDrawing.RouteIsSimple transformed :=
    inheritedSourceRoute_isSimple
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute sourceSimple
  have transformedFresh :
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline transformed) :=
    AxisDirection.lastNotInDropLast_unitSubdividePolyline_of_simple
      transformedOrthogonal transformedSimple
  have transformedLastRelative :
      transformedLast =
        Cell.add sourcePoint
          (Cell.scale PlanarOneInThree.gadgetScale
            (Cell.sub sourceLast sourceFirst)) := by
    rw [sourcePointEqual]
    rcases shift with ⟨shiftX, shiftY⟩
    rcases sourceFirst with ⟨firstX, firstY⟩
    rcases sourceLast with ⟨lastX, lastY⟩
    apply Prod.ext <;>
      simp [transformedLast, Cell.add, Cell.sub, Cell.scale] <;>
      ring
  have transformedLastNotInConnector :
      transformedLast ∉
        AxisDirection.unitSubdividePolyline connector := by
    intro member
    rw [connectorEqual,
      AxisDirection.unitSubdividePolyline_map_add] at member
    rw [transformedLastRelative] at member
    rcases List.mem_map.mp member with
      ⟨point, pointMember, pointEqual⟩
    have pointScaled :
        point =
          Cell.scale PlanarOneInThree.gadgetScale
            (Cell.sub sourceLast sourceFirst) :=
      Cell.add_left_injective sourcePoint pointEqual
    subst point
    have differenceZero :=
      sourceConnector_scaledGridPoint_eq_zero sourceLiteralIndex
        (Cell.sub sourceLast sourceFirst) pointMember
    apply sourceEndpointsDifferent
    rcases sourceFirst with ⟨firstX, firstY⟩
    rcases sourceLast with ⟨lastX, lastY⟩
    simp [Cell.sub] at differenceZero
    apply Prod.ext <;> omega
  apply
    AxisDirection.LastNotInDropLast.unitSubdividePolyline_joinAtEndpoint
      transformedFresh connectorNonempty transformedLength
      connectorOrthogonal transformedOrthogonal
      connectorGetLast transformedHead transformedGetLast
      transformedLastNotInConnector

end PeriodicOneInThreePositioned
end LeanTrominoes
