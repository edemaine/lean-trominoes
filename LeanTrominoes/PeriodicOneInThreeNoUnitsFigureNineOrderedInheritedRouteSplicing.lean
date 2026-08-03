import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineInheritedRouteSplicing
import LeanTrominoes.PositionedPeriodicCNFClauseExitFanOrdering

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

open PeriodicOrthocrossing

namespace ComposedClauseExitFanData

/-- Translate one finite fan connector from local composed-gadget
coordinates into an arbitrary clause gauge. -/
def translatedRoute
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (slot : Fin 3) : List Cell :=
  PeriodicOrthocrossing.translatePolyline origin (data.route slot)

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
