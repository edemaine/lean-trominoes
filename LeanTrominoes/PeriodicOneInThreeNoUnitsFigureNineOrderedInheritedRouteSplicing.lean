import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineInheritedRouteSplicing
import LeanTrominoes.PositionedPeriodicCNFClauseExitFanOrdering
import LeanTrominoes.OrthogonalPolylineStrictSeparation
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionScaling
import LeanTrominoes.OrthogonalPolylineRefinementStrictSeparation
import LeanTrominoes.OrthogonalPolylineSymmetries
import LeanTrominoes.ScaledPointNeighborhoodSeparation

/-!
# Splicing ordered composed exit fans to inherited routes

Clockwise clause ordering selects a certified finite fan from the three
composed Figure 9 source ports to the scaled first exits of the original
source routes.  This file translates one such fan into the canonical gauge
of a generated clause and uses it in place of the generic head detour.

The resulting suffix has exact composed-port and inherited-variable
endpoints and remains orthogonal.  Pairwise separation of the simultaneously
selected connectors is retained by the finite fan certificate and will be
used when the complete route family is assembled.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

namespace ComposedClauseExitFanData

/-- Translate one finite fan connector from local composed-gadget
coordinates into an arbitrary clause gauge. -/
def translatedRoute
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (slot : Fin 3) : List Cell :=
  PeriodicOrthocrossing.translatePolyline origin (data.route slot)

/-- Translate the connector together with its factor-two radial clearance
extension into an arbitrary clause gauge. -/
def translatedExtendedRoute
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (slot : Fin 3) : List Cell :=
  PeriodicOrthocrossing.translatePolyline origin
    (data.extendedRoute slot)

/-- The translated connector begins at its translated composed source
port. -/
@[simp]
theorem translatedRoute_head?
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (valid : data.IsValid)
    (slot : Fin 3)
    (active : data.SlotActive slot) :
    (data.translatedRoute origin slot).head? =
      some (Cell.add origin (sourceLocalPosition slot.val)) := by
  simp [translatedRoute,
    PeriodicOrthocrossing.translatePolyline,
    route_head? data valid slot active]

/-- The translated connector ends at the translated scaled source exit. -/
@[simp]
theorem translatedRoute_getLast?
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (valid : data.IsValid)
    (slot : Fin 3)
    (active : data.SlotActive slot) :
    (data.translatedRoute origin slot).getLast? =
      some (Cell.add origin (sourceExit (data.direction slot))) := by
  simp [translatedRoute,
    PeriodicOrthocrossing.translatePolyline,
    route_getLast? data valid slot active]

/-- Pointwise translation preserves connector orthogonality. -/
theorem translatedRoute_orthogonal
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (valid : data.IsValid)
    (slot : Fin 3)
    (active : data.SlotActive slot) :
    OrthogonalPolyline (data.translatedRoute origin slot) := by
  unfold OrthogonalPolyline at ⊢
  unfold translatedRoute PeriodicOrthocrossing.translatePolyline
  apply List.isChain_map_of_isChain (Cell.add origin)
  · intro first second aligned
    exact
      (GridSegment.isAxisAligned_translate
        (GridSegment.mk first second) origin).2 aligned
  · exact route_orthogonal data valid slot active

/-- Every translated connector stays in the radius-73 neighborhood of its
translated source-clause origin. -/
theorem translatedRoute_points_within_sourceNeighborhood
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (valid : data.IsValid)
    (slot : Fin 3)
    (active : data.SlotActive slot)
    {point : Cell}
    (pointMember : point ∈ data.translatedRoute origin slot) :
    WithinCoordinateRadius 73 origin point := by
  rcases List.mem_map.mp pointMember with
    ⟨sourcePoint, sourcePointMember, rfl⟩
  have sourceBounded :=
    route_points_within_sourceNeighborhood
      data valid slot active sourcePoint sourcePointMember
  simpa [Cell.add] using sourceBounded.translate origin

/-- Distinct active connectors remain strictly separated after their common
translation into a clause gauge. -/
theorem translatedRoutes_strictlyAvoidEachOther
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (valid : data.IsValid)
    (first second : Fin 3)
    (firstActive : data.SlotActive first)
    (secondActive : data.SlotActive second)
    (different : first ≠ second) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      (data.translatedRoute origin first)
      (data.translatedRoute origin second) := by
  exact
    (routes_strictlyAvoidEachOther
      data valid first second firstActive secondActive different).translatePolyline
        origin

end ComposedClauseExitFanData

/-- A transformed unit-step source route leaves its displayed clause point
at the radius-`72` exit selected by its original first direction. -/
theorem inheritedSourceRoute_tail_head?_of_unitSteps
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
            sourcePlacement sourceClause))
    (sourceTailNonempty :
      ∃ sourceExit, sourceRoute.tail.head? = some sourceExit)
    (sourceUnitSteps :
      sourceRoute.IsChain AxisDirection.IsUnitAxisStep) :
    (inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute).tail.head? =
        some
          (Cell.add
            (normalizedSourceClausePosition
              outputPlacement sourceClause generatedClause)
            (ComposedClauseExitFanData.sourceExit
              (AxisDirection.polylineFirstDirection sourceRoute))) := by
  cases sourceRoute with
  | nil =>
      simp at sourceTailNonempty
  | cons first rest =>
      cases rest with
      | nil =>
          simp at sourceTailNonempty
      | cons second rest =>
          have firstEq :
              first =
                PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause := by
            simpa using Option.some.inj sourceHead
          have firstUnit : AxisDirection.IsUnitAxisStep first second :=
            (List.isChain_cons_cons.mp sourceUnitSteps).1
          have secondEq :
              second =
                Cell.add first
                  (AxisDirection.between first second).step :=
            AxisDirection.add_between_step_eq_of_unitAxisStep firstUnit
          have transformedTail :=
            inheritedSourceRoute_tail_head?
              outputPlacement sourcePlacement sourceClause generatedClause
              (first :: second :: rest) second (by simp)
          rw [transformedTail]
          apply congrArg some
          change
            Cell.add
                (inheritedSourceRouteShift
                  outputPlacement sourcePlacement sourceClause
                  generatedClause)
                (Cell.scale composedGadgetScale second) =
              Cell.add
                (normalizedSourceClausePosition
                  outputPlacement sourceClause generatedClause)
                (Cell.scale composedGadgetScale
                  (AxisDirection.between first second).step)
          have scaledSecondEq :
              Cell.scale composedGadgetScale second =
                Cell.scale composedGadgetScale
                  (Cell.add first
                    (AxisDirection.between first second).step) :=
            congrArg (Cell.scale composedGadgetScale) secondEq
          rw [scaledSecondEq, firstEq]
          apply Prod.ext <;>
          simp [inheritedSourceRouteShift,
            Cell.add, Cell.sub, Cell.scale]
          <;> ring

/-- Replace the transformed source head by one connector from a certified
ordered composed exit fan. -/
def fanInheritedRouteSuffix
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
    (sourceRoute : List Cell) : List Cell :=
  let origin :=
    normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute
  replacePolylineHead
    (data.translatedRoute origin slot)
    transformed

/-- When the source route is the ordered subdivision of a doubled unit-step
route, the Figure 9 splice is exactly the radially extended connector joined
to the subdivision of the remaining doubled source route. -/
theorem fanInheritedRouteSuffix_eq_extended_join_farTail
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
      data.direction slot = AxisDirection.between first second) :
    fanInheritedRouteSuffix
        outputPlacement sourcePlacement sourceClause generatedClause
        data slot
        (AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (first :: second :: rest))) =
      joinAtEndpoint
        (data.translatedExtendedRoute
          (normalizedSourceClausePosition
            outputPlacement sourceClause generatedClause)
          slot)
        (PeriodicOrthocrossing.translatePolyline
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
  let radial :=
    PeriodicOrthocrossing.translatePolyline shift
      (scalePolyline composedGadgetScale
        [Cell.add (Cell.scale 2 first)
            (AxisDirection.between first second).step,
          Cell.scale 2 second])
  let farTail :=
    PeriodicOrthocrossing.translatePolyline shift
      (scalePolyline composedGadgetScale
        (AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (second :: rest))))
  have originEq :
      origin =
        Cell.add shift
          (Cell.scale composedGadgetScale (Cell.scale 2 first)) := by
    rw [scaledHead]
    apply Prod.ext <;>
      simp [origin, shift, inheritedSourceRouteShift,
        Cell.add, Cell.sub, Cell.scale]
  rcases firstUnit with ⟨direction, genuine, secondEq⟩
  have betweenEq :
      AxisDirection.between first second = direction := by
    rw [secondEq]
    exact AxisDirection.between_add_step first genuine
  have dataDirectionEq : data.direction slot = direction :=
    directionEq.trans betweenEq
  have firstUnitAgain :
      AxisDirection.IsUnitAxisStep first second :=
    ⟨direction, genuine, secondEq⟩
  have radialEq :
      radial =
        PeriodicOrthocrossing.translatePolyline origin
          [ComposedClauseExitFanData.sourceExit (data.direction slot),
            ComposedClauseExitFanData.outerSourceExit
              (data.direction slot)] := by
    rw [dataDirectionEq]
    simp only [radial]
    rw [betweenEq, secondEq]
    simp [originEq,
      ComposedClauseExitFanData.sourceExit,
      ComposedClauseExitFanData.outerSourceExit,
      PeriodicOrthocrossing.translatePolyline, scalePolyline,
      composedGadgetScale, Cell.add, Cell.scale]
    constructor <;> ring_nf <;> simp
  have scalePolyline_tail
      (factor : Int) (route : List Cell) :
      (scalePolyline factor route).tail =
        scalePolyline factor route.tail := by
    simp [scalePolyline]
  have transformedTailEq :
      (inheritedSourceRoute
        outputPlacement sourcePlacement sourceClause generatedClause
        (AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (first :: second :: rest)))).tail =
        joinAtEndpoint radial farTail := by
    rw [inheritedSourceRoute]
    unfold PeriodicOrthocrossing.translatePolyline
    rw [← List.map_tail, scalePolyline_tail]
    rw [AxisDirection.unitSubdividePolyline_scale_two_tail firstUnitAgain]
    simp [radial, farTail, shift,
      PeriodicOrthocrossing.translatePolyline,
      scalePolyline, joinAtEndpoint]
  have radialNe : radial ≠ [] := by
    rw [radialEq]
    simp [PeriodicOrthocrossing.translatePolyline]
  have extendedEq :
      data.translatedExtendedRoute origin slot =
        joinAtEndpoint (data.translatedRoute origin slot) radial := by
    rw [radialEq]
    simp [ComposedClauseExitFanData.translatedExtendedRoute,
      ComposedClauseExitFanData.translatedRoute,
      ComposedClauseExitFanData.extendedRoute,
      PeriodicOrthocrossing.translatePolyline,
      joinAtEndpoint, List.map_append]
  calc
    fanInheritedRouteSuffix
        outputPlacement sourcePlacement sourceClause generatedClause
        data slot
        (AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (first :: second :: rest))) =
      joinAtEndpoint (data.translatedRoute origin slot)
        (joinAtEndpoint radial farTail) := by
          rw [fanInheritedRouteSuffix, replacePolylineHead,
            transformedTailEq]
    _ = joinAtEndpoint
          (joinAtEndpoint (data.translatedRoute origin slot) radial)
          farTail :=
      joinAtEndpoint_assoc_of_middle_ne_nil radialNe
    _ = joinAtEndpoint (data.translatedExtendedRoute origin slot)
          farTail := by rw [extendedEq]

/-- A radius-72 local route strictly avoids the actual subdivided far tail
of a simple source route.  The coarse source tail is first separated at
factor 144, then the result is transported through factor-two unit
subdivision, factor-72 scaling, and translation. -/
theorem strictlyAvoids_translatedScaledDoubledSubdividedTail
    {first second : Cell} {rest nearby : List Cell}
    (shift : Cell)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (first :: second :: rest))
    (sourceSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (first :: second :: rest))
    (nearbyOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline nearby)
    (nearbyBounded :
      ∀ point ∈ nearby,
        WithinCoordinateRadius 72
          (Cell.add shift (Cell.scale 144 first)) point) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      nearby
      (PeriodicOrthocrossing.translatePolyline shift
        (scalePolyline composedGadgetScale
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (second :: rest))))) := by
  have tailAvoids :=
    sourceSimple.tail_avoids_head
      (head := first) (by rfl)
  have coarseSourceAvoidsNearby :=
    routesStrictlyAvoidEachOther_translateScalePolyline_pointNeighborhood
      (source := second :: rest) (nearby := nearby)
      (center := first) (offset := shift)
      (factor := 144) (radius := 72)
      (by norm_num) (by norm_num)
      (by simpa using tailAvoids.1)
      (by simpa using tailAvoids.2)
      nearbyBounded
  have tailOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline (second :: rest) :=
    (List.isChain_cons_cons.mp sourceOrthogonal).2
  have doubledTailOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (scalePolyline 2 (second :: rest)) :=
    tailOrthogonal.scalePolyline (by norm_num)
  have baseRefines :=
    AxisDirection.unitSubdividePolyline_refines
      doubledTailOrthogonal
  have scaledRefines :=
    PolylineRefines.scalePolyline
      (factor := composedGadgetScale)
      (by
        norm_num [composedGadgetScale, PlanarOneInThree.gadgetScale,
          PeriodicOneInThreeNoUnitsPositioned.gadgetScale])
      baseRefines
  have translatedRefines :=
    PolylineRefines.translatePolyline scaledRefines shift
  have farRefines :
      PolylineRefines
        (PeriodicOrthocrossing.translatePolyline shift
          (scalePolyline composedGadgetScale
            (AxisDirection.unitSubdividePolyline
              (scalePolyline 2 (second :: rest)))))
        (PeriodicOrthocrossing.translatePolyline shift
          (scalePolyline 144 (second :: rest))) := by
    simpa [scalePolyline, Cell.scale_scale,
      List.map_map, Function.comp_def,
      composedGadgetScale, PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale] using
      translatedRefines
  have coarseOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (PeriodicOrthocrossing.translatePolyline shift
          (scalePolyline 144 (second :: rest))) :=
    (tailOrthogonal.scalePolyline (factor := 144) (by norm_num)).translate
      shift
  exact
    coarseSourceAvoidsNearby.symm.refine_right
      nearbyOrthogonal coarseOrthogonal farRefines

/-- Strict separation from both pieces of an ordered inherited suffix
composes across the certified connector-to-source-route splice.  This lemma
isolates the reusable bookkeeping at the join: downstream geometry only has
to separate a route from the finite connector and from the unchanged tail of
the transformed source route. -/
theorem strictlyAvoids_fanInheritedRouteSuffix_of_connector_of_tail
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
    (sourceRoute localRoute : List Cell)
    (fanValid : data.IsValid)
    (slotActive : data.SlotActive slot)
    (directionEq :
      data.direction slot =
        AxisDirection.polylineFirstDirection sourceRoute)
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause))
    (sourceTailNonempty :
      ∃ sourceExit, sourceRoute.tail.head? = some sourceExit)
    (sourceUnitSteps :
      sourceRoute.IsChain AxisDirection.IsUnitAxisStep)
    (connectorAvoid :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
        localRoute
        (data.translatedRoute
          (normalizedSourceClausePosition
            outputPlacement sourceClause generatedClause)
          slot))
    (tailAvoid :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
        localRoute
        (inheritedSourceRoute
          outputPlacement sourcePlacement sourceClause generatedClause
          sourceRoute).tail) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      localRoute
      (fanInheritedRouteSuffix
        outputPlacement sourcePlacement sourceClause generatedClause
        data slot sourceRoute) := by
  let origin :=
    normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute
  have connectorLast :
      (data.translatedRoute origin slot).getLast? =
        some
          (Cell.add origin
            (ComposedClauseExitFanData.sourceExit
              (data.direction slot))) :=
    data.translatedRoute_getLast? origin fanValid slot slotActive
  have transformedTailHead :
      transformed.tail.head? =
        some
          (Cell.add origin
            (ComposedClauseExitFanData.sourceExit
              (data.direction slot))) := by
    rw [directionEq]
    exact
      inheritedSourceRoute_tail_head?_of_unitSteps
        outputPlacement sourcePlacement sourceClause generatedClause
        sourceRoute sourceHead sourceTailNonempty sourceUnitSteps
  unfold fanInheritedRouteSuffix replacePolylineHead
  exact
    connectorAvoid.join_right tailAvoid
      connectorLast transformedTailHead

/-- A valid selected fan connector splices to a matching unit-step source
route with exact canonical endpoints and preserved orthogonality. -/
theorem fanInheritedRouteSuffix_valid
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
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (sourceRoute : List Cell)
    (fanValid : data.IsValid)
    (slotActive : data.SlotActive slot)
    (directionEq :
      data.direction slot =
        AxisDirection.polylineFirstDirection sourceRoute)
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
      ∃ sourceExit, sourceRoute.tail.head? = some sourceExit)
    (sourceUnitSteps :
      sourceRoute.IsChain AxisDirection.IsUnitAxisStep)
    (literalAtom :
      generatedLiteral.atom = .inl (.inl sourceLiteral.atom))
    (literalOffset :
      generatedLiteral.offset = sourceLiteral.offset) :
    (fanInheritedRouteSuffix
        (composedPlacement source sourcePlacement)
        sourcePlacement sourceClause generatedClause
        data slot sourceRoute).head? =
        some
          (normalizedSourcePort
            (composedPlacement source sourcePlacement)
            sourceClause generatedClause slot.val) ∧
      (fanInheritedRouteSuffix
        (composedPlacement source sourcePlacement)
        sourcePlacement sourceClause generatedClause
        data slot sourceRoute).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (composedPlacement source sourcePlacement)
            generatedClause generatedLiteral) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (fanInheritedRouteSuffix
          (composedPlacement source sourcePlacement)
          sourcePlacement sourceClause generatedClause
          data slot sourceRoute) := by
  let origin :=
    normalizedSourceClausePosition
      (composedPlacement source sourcePlacement)
      sourceClause generatedClause
  let transformed :=
    inheritedSourceRoute
      (composedPlacement source sourcePlacement)
      sourcePlacement sourceClause generatedClause sourceRoute
  let connector := data.translatedRoute origin slot
  have transformedTailHead :
      transformed.tail.head? =
        some
          (Cell.add origin
            (ComposedClauseExitFanData.sourceExit
              (data.direction slot))) := by
    rw [directionEq]
    exact inheritedSourceRoute_tail_head?_of_unitSteps
      (composedPlacement source sourcePlacement)
      sourcePlacement sourceClause generatedClause
      sourceRoute sourceHead sourceTailNonempty sourceUnitSteps
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
  have connectorHead :
      connector.head? =
        some
          (normalizedSourcePort
            (composedPlacement source sourcePlacement)
            sourceClause generatedClause slot.val) := by
    simpa [connector, origin, normalizedSourcePort] using
      data.translatedRoute_head? origin fanValid slot slotActive
  have connectorLast :
      connector.getLast? =
        some
          (Cell.add origin
            (ComposedClauseExitFanData.sourceExit
              (data.direction slot))) :=
    data.translatedRoute_getLast? origin fanValid slot slotActive
  change
    (replacePolylineHead connector transformed).head? = _ ∧
      (replacePolylineHead connector transformed).getLast? = _ ∧
      OrthogonalPolyline (replacePolylineHead connector transformed)
  exact
    ⟨replacePolylineHead_head? connectorHead,
      replacePolylineHead_getLast?
        connectorLast transformedTailHead transformedLast,
      (data.translatedRoute_orthogonal
        origin fanValid slot slotActive).replaceHead
          (inheritedSourceRoute_orthogonal
            (composedPlacement source sourcePlacement)
            sourcePlacement sourceClause generatedClause
            sourceRoute sourceOrthogonal)
          connectorLast transformedTailHead⟩

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
