/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineHeadReplacement
import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.OrthogonalPolylineHeadReplacementEndpointDirections
import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedEndpoints
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Splicing unit-elimination ports to inherited routes

This file scales a source incidence route by the unit-elimination refinement
factor, translates it into a generated clause's canonical anchor gauge, and
replaces its obsolete source-clause endpoint by a route from the appropriate
local boundary port to the transformed first exit.
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

/-- Source incidences from the same unit-elimination block use one common
translation after refinement.  Generated clauses in that block may differ,
but their common logical anchor gives the same normalized source origin. -/
theorem inheritedSourceRouteShift_eq_of_sourceClause_eq_of_anchor_eq
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (firstSourceClause secondSourceClause :
      PositionedPeriodicClause Variable)
    (firstGeneratedClause secondGeneratedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceClausesEqual : firstSourceClause = secondSourceClause)
    (anchorsEqual :
      PeriodicCNF.clauseAnchor firstGeneratedClause.literals =
        PeriodicCNF.clauseAnchor secondGeneratedClause.literals) :
    inheritedSourceRouteShift
        outputPlacement sourcePlacement
        firstSourceClause firstGeneratedClause =
      inheritedSourceRouteShift
        outputPlacement sourcePlacement
        secondSourceClause secondGeneratedClause := by
  subst secondSourceClause
  unfold inheritedSourceRouteShift
  rw [normalizedSourceClausePosition_eq_of_anchor_eq
    outputPlacement firstSourceClause
    firstGeneratedClause secondGeneratedClause anchorsEqual]

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

/-- Deleting the obsolete heads of two simple separated source routes and
then applying one common inherited-route transform preserves separation;
all surviving listed contacts are at their variable-side tails. -/
theorem inheritedSourceRoute_tails_separated_of_common_shift
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (firstSourceClause secondSourceClause :
      PositionedPeriodicClause Variable)
    (firstGeneratedClause secondGeneratedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (firstSourceRoute secondSourceRoute : List Cell)
    (shiftsEqual :
      inheritedSourceRouteShift
          outputPlacement sourcePlacement
          firstSourceClause firstGeneratedClause =
        inheritedSourceRouteShift
          outputPlacement sourcePlacement
          secondSourceClause secondGeneratedClause)
    (sourceAvoid :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        firstSourceRoute secondSourceRoute)
    (firstNodup : firstSourceRoute.Nodup)
    (secondNodup : secondSourceRoute.Nodup) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        (inheritedSourceRoute
          outputPlacement sourcePlacement
          firstSourceClause firstGeneratedClause
          firstSourceRoute).tail
        (inheritedSourceRoute
          outputPlacement sourcePlacement
          secondSourceClause secondGeneratedClause
          secondSourceRoute).tail ∧
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtTails
        (inheritedSourceRoute
          outputPlacement sourcePlacement
          firstSourceClause firstGeneratedClause
          firstSourceRoute).tail
        (inheritedSourceRoute
          outputPlacement sourcePlacement
          secondSourceClause secondGeneratedClause
          secondSourceRoute).tail := by
  open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing in
    have tailAvoid :
        RoutesAvoidEachOther firstSourceRoute.tail secondSourceRoute.tail :=
      routesAvoidEachOther_tail_of_avoid_of_nodup
        sourceAvoid firstNodup secondNodup
  open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing in
    have tailContacts :
        RoutesMeetOnlyAtTails firstSourceRoute.tail secondSourceRoute.tail :=
      routesMeetOnlyAtTails_tail_of_avoid_of_nodup
        sourceAvoid firstNodup secondNodup
  open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing in
    have scaledAvoid :=
      tailAvoid.scalePolyline (factor := gadgetScale) (by decide)
  open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing in
    have scaledContacts :=
      tailContacts.scalePolyline (factor := gadgetScale) (by decide)
  open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing in
    have translatedAvoid :=
      routesAvoidEachOther_translate scaledAvoid
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement
          firstSourceClause firstGeneratedClause)
  open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing in
    have translatedContacts :=
      scaledContacts.translate
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement
          firstSourceClause firstGeneratedClause)
  simpa [inheritedSourceRoute,
    PeriodicOrthocrossing.translatePolyline,
    scalePolyline, ← shiftsEqual] using
    And.intro translatedAvoid translatedContacts

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

/-- Refinement and anchor-gauge translation preserve the direction in which
an inherited route enters its source variable. -/
@[simp]
theorem inheritedSourceRoute_lastDirection
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceRoute : List Cell) :
    AxisDirection.polylineLastDirection
        (inheritedSourceRoute
          outputPlacement sourcePlacement sourceClause generatedClause
          sourceRoute) =
      AxisDirection.polylineLastDirection sourceRoute := by
  rw [show
    inheritedSourceRoute
        outputPlacement sourcePlacement sourceClause generatedClause
        sourceRoute =
      PeriodicOrthocrossing.translatePolyline
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement sourceClause generatedClause)
        (scalePolyline gadgetScale sourceRoute) by
      rfl]
  rw [AxisDirection.polylineLastDirection_translatePolyline]
  exact
    AxisDirection.polylineLastDirection_scalePolyline
      gadgetScale (by decide) sourceRoute

/-- Scaling and changing the anchor gauge carry a source route's first exit
to the correspondingly transformed point. -/
theorem inheritedSourceRoute_tail_head?
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
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
              outputPlacement sourcePlacement sourceClause generatedClause)
            (Cell.scale gadgetScale sourceExit)) := by
  simpa [inheritedSourceRoute,
    PeriodicOrthocrossing.translatePolyline,
    scalePolyline] using
    List.tail_head?_map
      (Cell.add
        (inheritedSourceRouteShift
          outputPlacement sourcePlacement sourceClause generatedClause))
      (List.tail_head?_map
        (Cell.scale gadgetScale) sourceTailHead)

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

/-- Replacing the transformed source route's clause-side prefix leaves its
variable-side terminal direction unchanged on every route with at least
three points. -/
theorem inheritedRouteSuffix_lastDirection
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceLiteralIndex : Nat)
    (sourceRoute : List Cell)
    (sourceLength : 3 ≤ sourceRoute.length) :
    AxisDirection.polylineLastDirection
        (inheritedRouteSuffix
          outputPlacement sourcePlacement sourceClause generatedClause
          sourceLiteralIndex sourceRoute) =
      AxisDirection.polylineLastDirection sourceRoute := by
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute
  have transformedLength : 3 ≤ transformed.length := by
    simpa [transformed, inheritedSourceRoute,
      PeriodicOrthocrossing.translatePolyline,
      scalePolyline] using sourceLength
  have tailNonempty :
      ∃ exit, transformed.tail.head? = some exit := by
    rcases transformed with _ | ⟨first, rest⟩
    · simp at transformedLength
    · rcases rest with _ | ⟨second, rest⟩
      · simp at transformedLength
      · exact ⟨second, rfl⟩
  have tailHead :=
    polylineFirstExit_spec tailNonempty
  rw [show
    inheritedRouteSuffix
        outputPlacement sourcePlacement sourceClause generatedClause
        sourceLiteralIndex sourceRoute =
      replacePolylineHead
        (PositionedPeriodicCNF.orthogonalDetour
          (normalizedSourcePort outputPlacement sourceClause
            generatedClause sourceLiteralIndex)
          (polylineFirstExit transformed))
        transformed by
      rfl]
  rw [AxisDirection.polylineLastDirection_replacePolylineHead
    (PositionedPeriodicCNF.orthogonalDetour_getLast? _ _)
    tailHead transformedLength]
  exact inheritedSourceRoute_lastDirection
    outputPlacement sourcePlacement sourceClause generatedClause
    sourceRoute

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
    (sourceTailNonempty :
      ∃ sourceExit,
        sourceRoute.tail.head? = some sourceExit)
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
  let transformed : List Cell :=
    inheritedSourceRoute
      (placement source sourcePlacement)
      sourcePlacement sourceClause generatedClause sourceRoute
  have _transformedHead :
      transformed.head? =
        some
          (normalizedSourceClausePosition
            (placement source sourcePlacement)
            sourceClause generatedClause) :=
    inheritedSourceRoute_head?
      (placement source sourcePlacement)
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
            (placement source sourcePlacement)
            sourcePlacement sourceClause generatedClause)
          (Cell.scale gadgetScale sourceExit),
        inheritedSourceRoute_tail_head?
          (placement source sourcePlacement)
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
            (placement source sourcePlacement)
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
              (placement source sourcePlacement)
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
            (placement source sourcePlacement)
            sourcePlacement sourceClause generatedClause
            sourceRoute sourceOrthogonal)
          (by simp) transformedTailHead⟩

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
