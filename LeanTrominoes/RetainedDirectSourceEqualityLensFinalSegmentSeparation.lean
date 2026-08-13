/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceCompleteTails
import LeanTrominoes.PlanarThreeSATEqualityLensCarrierInterface
import LeanTrominoes.PolylineBoundingBoxRasterSeparation

/-!
# Direct terminal rectangles at equality-lens contacts

The only oblique direct atlas segments that reach a macrocell carrier
boundary end at that boundary's compass port.  Comparing this finite fact
with the four parametric equality-lens suffixes shows that nonseparated
terminal rectangles force the two routes to have the same final endpoint.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

set_option maxHeartbeats 2000000

private instance decidableForallFintype
    {α : Type*} [Fintype α]
    (predicate : α → Prop)
    [∀ value, Decidable (predicate value)] :
    Decidable (∀ value, predicate value) :=
  Fintype.decidableForallFintype

/-- An oblique direct atlas segment is strictly inside each side of its
`12 × 12` local frame unless its final endpoint is that side's carrier
port. -/
theorem retainedDirectSourceLocalSegment_strictlyInside_or_finish_eq_port :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (port : CornerPort),
      let segment : GridSegment :=
        ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
      ¬segment.IsAxisAligned →
        1 ≤ segment.coordinateLower.1 ∧
          segment.coordinateUpper.1 ≤ 11 ∧
          1 ≤ segment.coordinateLower.2 ∧
          segment.coordinateUpper.2 ≤ 11 ∧
          match port with
          | .west =>
              1 < segment.coordinateLower.1 ∨
                segment.finish = (1, 6)
          | .east =>
              segment.coordinateUpper.1 < 11 ∨
                segment.finish = (11, 6)
          | .south =>
              1 < segment.coordinateLower.2 ∨
                segment.finish = (6, 1)
          | .north =>
              segment.coordinateUpper.2 < 11 ∨
                segment.finish = (6, 11) := by
  intro kind index port
  cases kind with
  | crossover clauseIndex =>
      fin_cases clauseIndex <;>
        fin_cases index <;>
        cases port <;>
        native_decide
  | duplicator arm clauseIndex =>
      cases arm <;>
        fin_cases clauseIndex <;>
        fin_cases index <;>
        cases port <;>
        native_decide
  | routedClause =>
      fin_cases index <;>
        cases port <;>
        native_decide

/-- Translating a segment translates the lower corner of its endpoint
rectangle by the same vector. -/
theorem GridSegment.coordinateLower_translate
    (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).coordinateLower =
      Cell.add offset segment.coordinateLower := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [GridSegment.translate, GridSegment.coordinateLower,
    Cell.add, min_def]
  split_ifs <;> omega

/-- Translating a segment translates the upper corner of its endpoint
rectangle by the same vector. -/
theorem GridSegment.coordinateUpper_translate
    (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).coordinateUpper =
      Cell.add offset segment.coordinateUpper := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [GridSegment.translate, GridSegment.coordinateUpper,
    Cell.add, max_def]
  split_ifs <;> omega

/-- Translating two segments together preserves strict separation of their
closed endpoint rectangles. -/
private theorem coordinateRectanglesSeparated_translate_iff
    (first second : GridSegment) (offset : Cell) :
    ClosedGridRectanglesSeparated
        (first.translate offset).coordinateLower
        (first.translate offset).coordinateUpper
        (second.translate offset).coordinateLower
        (second.translate offset).coordinateUpper ↔
      ClosedGridRectanglesSeparated
        first.coordinateLower first.coordinateUpper
        second.coordinateLower second.coordinateUpper := by
  rw [GridSegment.coordinateLower_translate,
    GridSegment.coordinateUpper_translate,
    GridSegment.coordinateLower_translate,
    GridSegment.coordinateUpper_translate]
  rcases first.coordinateLower with ⟨firstLowerX, firstLowerY⟩
  rcases first.coordinateUpper with ⟨firstUpperX, firstUpperY⟩
  rcases second.coordinateLower with ⟨secondLowerX, secondLowerY⟩
  rcases second.coordinateUpper with ⟨secondUpperX, secondUpperY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp only [ClosedGridRectanglesSeparated, Cell.add]
  omega

/-- Exact finite certificate for the first-end terminal geometry in the
zero-origin lens.  The nearby lens suffixes are independent of the span. -/
private theorem axisEqualityLensDrawing_first_nearTerminal_zero :
    ∀ (direction : AxisDirection)
      (carrierClauseIndex : Fin 2)
      (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      let carrierRoute :=
        (axisEqualityLensDrawing (0, 0) direction 8).routes
          carrierClauseIndex 0
      let carrierFinal : GridSegment :=
        ⟨polylineLastEntrance carrierRoute,
          carrierRoute.getLastD (0, 0)⟩
      let directFinal :=
        (⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
            (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
          GridSegment).translate
            (AxisDirection.firstCarrierMacroOrigin (0, 0) direction)
      ¬(⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned →
        ClosedGridRectanglesSeparated
            carrierFinal.coordinateLower carrierFinal.coordinateUpper
            directFinal.coordinateLower directFinal.coordinateUpper ∨
          carrierFinal.finish = directFinal.finish := by
  native_decide

/-- A first-end lens terminal segment is the zero-origin terminal segment
translated by the lens origin. -/
private theorem axisEqualityLensDrawing_first_nearTerminal_translate
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (carrierClauseIndex : Fin 2) :
    let actualRoute :=
      (axisEqualityLensDrawing origin direction span).routes
        carrierClauseIndex 0
    let zeroRoute :=
      (axisEqualityLensDrawing (0, 0) direction 8).routes
        carrierClauseIndex 0
    (⟨polylineLastEntrance actualRoute,
        actualRoute.getLastD (0, 0)⟩ : GridSegment) =
      (⟨polylineLastEntrance zeroRoute,
          zeroRoute.getLastD (0, 0)⟩ : GridSegment).translate origin := by
  dsimp only
  fin_cases carrierClauseIndex <;>
    cases direction <;>
    rcases origin with ⟨originX, originY⟩ <;>
    simp [axisEqualityLensDrawing,
      EmbeddedCNFIncidenceDrawing.placeOnAxis,
      EmbeddedCNFIncidenceDrawing.translate,
      EmbeddedCNFIncidenceDrawing.orient,
      EmbeddedCNFIncidenceDrawing.mapPoints,
      horizontalEqualityLensDrawing,
      horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensLowerLeftRoute,
      AxisDirection.orientPoint, GridSegment.translate,
      polylineLastEntrance, polylineFirstExit, Cell.add]

/-- The direct segment placed at a first carrier macrocell is likewise a
translate of its zero-origin placement. -/
private theorem firstCarrierMacroOrigin_translate_segment
    (origin : Cell) (direction : AxisDirection)
    (segment : GridSegment) :
    segment.translate
        (AxisDirection.firstCarrierMacroOrigin origin direction) =
      (segment.translate
          (AxisDirection.firstCarrierMacroOrigin (0, 0) direction)).translate
        origin := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases origin with ⟨originX, originY⟩
  cases direction <;>
    simp [AxisDirection.firstCarrierMacroOrigin,
      AxisDirection.firstCarrierPort, CornerPort.position,
      GridSegment.translate, Cell.add, Cell.sub] <;>
    ring_nf <;>
    simp

/-- The two lens routes incident to the first endpoint meet an oblique
direct segment only when that direct segment ends at the endpoint. -/
private theorem axisEqualityLensDrawing_first_nearTerminal
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (carrierClauseIndex : Fin 2)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directOblique :
      ¬(⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierRoute :=
      (axisEqualityLensDrawing origin direction span).routes
        carrierClauseIndex 0
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierRoute,
        carrierRoute.getLastD (0, 0)⟩
    let directFinal :=
      (⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).translate
          (AxisDirection.firstCarrierMacroOrigin origin direction)
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        directFinal.coordinateLower directFinal.coordinateUpper ∨
      carrierFinal.finish = directFinal.finish := by
  let localDirect : GridSegment :=
    ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
      (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
  let actualRoute :=
    (axisEqualityLensDrawing origin direction span).routes
      carrierClauseIndex 0
  let actualCarrier : GridSegment :=
    ⟨polylineLastEntrance actualRoute,
      actualRoute.getLastD (0, 0)⟩
  let zeroRoute :=
    (axisEqualityLensDrawing (0, 0) direction 8).routes
      carrierClauseIndex 0
  let zeroCarrier : GridSegment :=
    ⟨polylineLastEntrance zeroRoute,
      zeroRoute.getLastD (0, 0)⟩
  let actualDirect := localDirect.translate
    (AxisDirection.firstCarrierMacroOrigin origin direction)
  let zeroDirect := localDirect.translate
    (AxisDirection.firstCarrierMacroOrigin (0, 0) direction)
  change
    ClosedGridRectanglesSeparated
        actualCarrier.coordinateLower actualCarrier.coordinateUpper
        actualDirect.coordinateLower actualDirect.coordinateUpper ∨
      actualCarrier.finish = actualDirect.finish
  have carrierTranslate :
      actualCarrier = zeroCarrier.translate origin := by
    exact axisEqualityLensDrawing_first_nearTerminal_translate
      origin direction span carrierClauseIndex
  have directTranslate :
      actualDirect = zeroDirect.translate origin := by
    exact firstCarrierMacroOrigin_translate_segment
      origin direction localDirect
  have finiteCertificate :=
    axisEqualityLensDrawing_first_nearTerminal_zero
      direction carrierClauseIndex kind index directOblique
  change
    ClosedGridRectanglesSeparated
        zeroCarrier.coordinateLower zeroCarrier.coordinateUpper
        zeroDirect.coordinateLower zeroDirect.coordinateUpper ∨
      zeroCarrier.finish = zeroDirect.finish
    at finiteCertificate
  rcases finiteCertificate with separated | finishes
  · left
    rw [carrierTranslate, directTranslate]
    exact
      (coordinateRectanglesSeparated_translate_iff
        zeroCarrier zeroDirect origin).2 separated
  · right
    rw [carrierTranslate, directTranslate]
    exact congrArg (Cell.add origin) finishes

/-- At the first endpoint of a placed equality lens, an oblique direct
segment has a separated terminal rectangle from every lens route unless
both routes finish at that endpoint. -/
theorem
    axisEqualityLensDrawing_first_finalSegmentRectanglesSeparated_or_finish_eq
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (spanLarge : 8 ≤ span)
    (carrierClauseIndex carrierLiteralIndex : Fin 2)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directOblique :
      ¬(⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierRoute :=
      (axisEqualityLensDrawing origin direction span).routes
        carrierClauseIndex carrierLiteralIndex
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierRoute,
        carrierRoute.getLastD (0, 0)⟩
    let directFinal :=
      (⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).translate
          (AxisDirection.firstCarrierMacroOrigin origin direction)
    ClosedGridRectanglesSeparated
      carrierFinal.coordinateLower carrierFinal.coordinateUpper
        directFinal.coordinateLower directFinal.coordinateUpper ∨
      carrierFinal.finish = directFinal.finish := by
  fin_cases carrierLiteralIndex
  · exact axisEqualityLensDrawing_first_nearTerminal
      origin direction span carrierClauseIndex kind index directOblique
  · dsimp only
    let localDirect : GridSegment :=
      ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
        (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
    have boundary :=
      retainedDirectSourceLocalSegment_strictlyInside_or_finish_eq_port
        kind index (AxisDirection.firstCarrierPort direction)
        directOblique
    by_cases separated :
        ClosedGridRectanglesSeparated
          (⟨polylineLastEntrance
                ((axisEqualityLensDrawing origin direction span).routes
                  carrierClauseIndex 1),
              ((axisEqualityLensDrawing origin direction span).routes
                carrierClauseIndex 1).getLastD (0, 0)⟩ :
            GridSegment).coordinateLower
          (⟨polylineLastEntrance
                ((axisEqualityLensDrawing origin direction span).routes
                  carrierClauseIndex 1),
              ((axisEqualityLensDrawing origin direction span).routes
                carrierClauseIndex 1).getLastD (0, 0)⟩ :
            GridSegment).coordinateUpper
          (localDirect.translate
            (AxisDirection.firstCarrierMacroOrigin
              origin direction)).coordinateLower
          (localDirect.translate
            (AxisDirection.firstCarrierMacroOrigin
              origin direction)).coordinateUpper
    · exact Or.inl separated
    · right
      fin_cases carrierClauseIndex <;>
        cases direction <;>
        rcases origin with ⟨originX, originY⟩ <;>
        simp [axisEqualityLensDrawing,
          EmbeddedCNFIncidenceDrawing.placeOnAxis,
          EmbeddedCNFIncidenceDrawing.translate,
          EmbeddedCNFIncidenceDrawing.orient,
          EmbeddedCNFIncidenceDrawing.mapPoints,
          horizontalEqualityLensDrawing,
          horizontalEqualityLensRoutes,
          horizontalEqualityLensUpperRightRoute,
          horizontalEqualityLensLowerRightRoute,
          AxisDirection.firstCarrierPort,
          AxisDirection.firstCarrierMacroOrigin,
          AxisDirection.orientPoint, CornerPort.position,
          GridSegment.translate, GridSegment.coordinateLower,
          GridSegment.coordinateUpper, ClosedGridRectanglesSeparated,
          Cell.add, Cell.sub,
          polylineLastEntrance, polylineFirstExit,
          min_def, max_def, localDirect] at boundary separated ⊢ <;>
        omega

/-- Every route using the second endpoint has that endpoint as its final
point. -/
private theorem axisEqualityLensDrawing_second_nearTerminal_finish
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (carrierClauseIndex : Fin 2) :
    let route :=
      (axisEqualityLensDrawing origin direction span).routes
        carrierClauseIndex 1
    (⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩ : GridSegment).finish =
      direction.placePoint origin (span, 0) := by
  dsimp only
  fin_cases carrierClauseIndex <;>
    cases direction <;>
    rcases origin with ⟨originX, originY⟩ <;>
    simp [axisEqualityLensDrawing,
      EmbeddedCNFIncidenceDrawing.placeOnAxis,
      EmbeddedCNFIncidenceDrawing.translate,
      EmbeddedCNFIncidenceDrawing.orient,
      EmbeddedCNFIncidenceDrawing.mapPoints,
      horizontalEqualityLensDrawing,
      horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerRightRoute,
      AxisDirection.placePoint, AxisDirection.orientPoint,
      Cell.add]

/-- The two lens routes incident to the second endpoint meet an oblique
direct segment only when that direct segment ends at the endpoint. -/
private theorem axisEqualityLensDrawing_second_nearTerminal
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (spanLarge : 8 ≤ span)
    (carrierClauseIndex : Fin 2)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directOblique :
      ¬(⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierRoute :=
      (axisEqualityLensDrawing origin direction span).routes
        carrierClauseIndex 1
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierRoute,
        carrierRoute.getLastD (0, 0)⟩
    let directFinal :=
      (⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).translate
          (AxisDirection.secondCarrierMacroOrigin
            origin direction span)
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        directFinal.coordinateLower directFinal.coordinateUpper ∨
      carrierFinal.finish = directFinal.finish := by
  dsimp only
  let localDirect : GridSegment :=
    ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
      (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
  have boundary :=
    retainedDirectSourceLocalSegment_strictlyInside_or_finish_eq_port
      kind index (AxisDirection.secondCarrierPort direction)
      directOblique
  rcases boundary with
    ⟨lowerX, upperX, lowerY, upperY, side⟩
  have carrierFinish :=
    axisEqualityLensDrawing_second_nearTerminal_finish
      origin direction span carrierClauseIndex
  dsimp only at carrierFinish
  cases direction <;>
    simp only [AxisDirection.secondCarrierPort] at side
  all_goals
    rcases side with strict | endpoint
    · left
      fin_cases carrierClauseIndex <;>
        rcases origin with ⟨originX, originY⟩ <;>
        simp [axisEqualityLensDrawing,
          EmbeddedCNFIncidenceDrawing.placeOnAxis,
          EmbeddedCNFIncidenceDrawing.translate,
          EmbeddedCNFIncidenceDrawing.orient,
          EmbeddedCNFIncidenceDrawing.mapPoints,
          horizontalEqualityLensDrawing,
          horizontalEqualityLensRoutes,
          horizontalEqualityLensUpperRightRoute,
          horizontalEqualityLensLowerRightRoute,
          AxisDirection.secondCarrierPort,
          AxisDirection.secondCarrierMacroOrigin,
          AxisDirection.placePoint, AxisDirection.orientPoint,
          CornerPort.position,
          GridSegment.translate, GridSegment.coordinateLower,
          GridSegment.coordinateUpper, ClosedGridRectanglesSeparated,
          Cell.add, Cell.sub,
          polylineLastEntrance, polylineFirstExit,
          min_def, max_def]
          at lowerX upperX lowerY upperY strict ⊢ <;>
        omega
    · right
      rw [carrierFinish]
      rcases origin with ⟨originX, originY⟩
      have endpointX := congrArg Prod.fst endpoint
      have endpointY := congrArg Prod.snd endpoint
      simp [GridSegment.translate,
        AxisDirection.secondCarrierMacroOrigin,
        AxisDirection.secondCarrierPort,
        AxisDirection.placePoint, AxisDirection.orientPoint,
        CornerPort.position, Cell.add, Cell.sub]
        at endpointX endpointY ⊢
      omega

/-- The analogous terminal-rectangle dichotomy at the second endpoint of a
placed equality lens. -/
theorem
    axisEqualityLensDrawing_second_finalSegmentRectanglesSeparated_or_finish_eq
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (spanLarge : 8 ≤ span)
    (carrierClauseIndex carrierLiteralIndex : Fin 2)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directOblique :
      ¬(⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierRoute :=
      (axisEqualityLensDrawing origin direction span).routes
        carrierClauseIndex carrierLiteralIndex
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierRoute,
        carrierRoute.getLastD (0, 0)⟩
    let directFinal :=
      (⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).translate
          (AxisDirection.secondCarrierMacroOrigin
            origin direction span)
    ClosedGridRectanglesSeparated
      carrierFinal.coordinateLower carrierFinal.coordinateUpper
        directFinal.coordinateLower directFinal.coordinateUpper ∨
      carrierFinal.finish = directFinal.finish := by
  fin_cases carrierLiteralIndex
  · dsimp only
    let localDirect : GridSegment :=
      ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
        (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
    have boundary :=
      retainedDirectSourceLocalSegment_strictlyInside_or_finish_eq_port
        kind index (AxisDirection.secondCarrierPort direction)
        directOblique
    by_cases separated :
        ClosedGridRectanglesSeparated
          (⟨polylineLastEntrance
                ((axisEqualityLensDrawing origin direction span).routes
                  carrierClauseIndex 0),
              ((axisEqualityLensDrawing origin direction span).routes
                carrierClauseIndex 0).getLastD (0, 0)⟩ :
            GridSegment).coordinateLower
          (⟨polylineLastEntrance
                ((axisEqualityLensDrawing origin direction span).routes
                  carrierClauseIndex 0),
              ((axisEqualityLensDrawing origin direction span).routes
                carrierClauseIndex 0).getLastD (0, 0)⟩ :
            GridSegment).coordinateUpper
          (localDirect.translate
            (AxisDirection.secondCarrierMacroOrigin
              origin direction span)).coordinateLower
          (localDirect.translate
            (AxisDirection.secondCarrierMacroOrigin
              origin direction span)).coordinateUpper
    · exact Or.inl separated
    · right
      fin_cases carrierClauseIndex <;>
        cases direction <;>
        rcases origin with ⟨originX, originY⟩ <;>
        simp [axisEqualityLensDrawing,
          EmbeddedCNFIncidenceDrawing.placeOnAxis,
          EmbeddedCNFIncidenceDrawing.translate,
          EmbeddedCNFIncidenceDrawing.orient,
          EmbeddedCNFIncidenceDrawing.mapPoints,
          horizontalEqualityLensDrawing,
          horizontalEqualityLensRoutes,
          horizontalEqualityLensUpperLeftRoute,
          horizontalEqualityLensLowerLeftRoute,
          AxisDirection.secondCarrierPort,
          AxisDirection.secondCarrierMacroOrigin,
          AxisDirection.placePoint, AxisDirection.orientPoint,
          CornerPort.position,
          GridSegment.translate, GridSegment.coordinateLower,
          GridSegment.coordinateUpper, ClosedGridRectanglesSeparated,
          Cell.add, Cell.sub,
          polylineLastEntrance, polylineFirstExit,
          min_def, max_def, localDirect] at boundary separated ⊢ <;>
        omega
  · exact axisEqualityLensDrawing_second_nearTerminal
      origin direction span spanLarge carrierClauseIndex kind index
      directOblique

/-- The first-end terminal dichotomy in the intrinsic coordinates of a
geometrically certified equality link. -/
theorem EqualityLink.lensDrawing_first_finalSegmentRectanglesSeparated_or_finish_eq
    {Variable : Type*} [DecidableEq Variable]
    {position : Variable → Cell}
    {link : EqualityLink Variable}
    (geometry : EqualityLink.LensGeometry position link)
    (carrierClauseIndex carrierLiteralIndex : Fin 2)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directOblique :
      ¬(⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierRoute :=
      (EqualityLink.lensDrawing position link).routes
        carrierClauseIndex carrierLiteralIndex
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierRoute,
        carrierRoute.getLastD (0, 0)⟩
    let directFinal :=
      (⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).translate
          (EqualityLink.firstCarrierMacroOrigin position link)
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        directFinal.coordinateLower directFinal.coordinateUpper ∨
      carrierFinal.finish = directFinal.finish := by
  simpa [EqualityLink.lensDrawing,
    placedEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EqualityLink.firstCarrierMacroOrigin,
    EqualityLink.carrierDirection,
    EqualityLink.carrierSpan] using
      axisEqualityLensDrawing_first_finalSegmentRectanglesSeparated_or_finish_eq
        (position link.first)
        (AxisDirection.between
          (position link.first) (position link.second))
        (AxisDirection.axisSpan
          (position link.first) (position link.second))
        geometry.spanLarge carrierClauseIndex carrierLiteralIndex
        kind index directOblique

/-- The analogous intrinsic dichotomy at the second endpoint of a certified
equality link. -/
theorem EqualityLink.lensDrawing_second_finalSegmentRectanglesSeparated_or_finish_eq
    {Variable : Type*} [DecidableEq Variable]
    {position : Variable → Cell}
    {link : EqualityLink Variable}
    (geometry : EqualityLink.LensGeometry position link)
    (carrierClauseIndex carrierLiteralIndex : Fin 2)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directOblique :
      ¬(⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierRoute :=
      (EqualityLink.lensDrawing position link).routes
        carrierClauseIndex carrierLiteralIndex
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierRoute,
        carrierRoute.getLastD (0, 0)⟩
    let directFinal :=
      (⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).translate
          (EqualityLink.secondCarrierMacroOrigin position link)
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        directFinal.coordinateLower directFinal.coordinateUpper ∨
      carrierFinal.finish = directFinal.finish := by
  simpa [EqualityLink.lensDrawing,
    placedEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EqualityLink.secondCarrierMacroOrigin,
    EqualityLink.carrierDirection,
    EqualityLink.carrierSpan] using
      axisEqualityLensDrawing_second_finalSegmentRectanglesSeparated_or_finish_eq
        (position link.first)
        (AxisDirection.between
          (position link.first) (position link.second))
        (AxisDirection.axisSpan
          (position link.first) (position link.second))
        geometry.spanLarge carrierClauseIndex carrierLiteralIndex
        kind index directOblique

/-- Natural-index interface for the intrinsic first-end dichotomy. -/
theorem EqualityLink.lensDrawing_first_finalSegmentRectanglesSeparated_or_finish_eq_nat
    {Variable : Type*} [DecidableEq Variable]
    {position : Variable → Cell}
    {link : EqualityLink Variable}
    (geometry : EqualityLink.LensGeometry position link)
    (carrierClauseIndex carrierLiteralIndex : Nat)
    (carrierClauseIndexLt : carrierClauseIndex < 2)
    (carrierLiteralIndexLt : carrierLiteralIndex < 2)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directOblique :
      ¬(⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierRoute :=
      (EqualityLink.lensDrawing position link).routes
        carrierClauseIndex carrierLiteralIndex
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierRoute,
        carrierRoute.getLastD (0, 0)⟩
    let directFinal :=
      (⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).translate
          (EqualityLink.firstCarrierMacroOrigin position link)
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        directFinal.coordinateLower directFinal.coordinateUpper ∨
      carrierFinal.finish = directFinal.finish := by
  exact
    EqualityLink.lensDrawing_first_finalSegmentRectanglesSeparated_or_finish_eq
      geometry ⟨carrierClauseIndex, carrierClauseIndexLt⟩
      ⟨carrierLiteralIndex, carrierLiteralIndexLt⟩
      kind index directOblique

/-- Natural-index interface for the intrinsic second-end dichotomy. -/
theorem EqualityLink.lensDrawing_second_finalSegmentRectanglesSeparated_or_finish_eq_nat
    {Variable : Type*} [DecidableEq Variable]
    {position : Variable → Cell}
    {link : EqualityLink Variable}
    (geometry : EqualityLink.LensGeometry position link)
    (carrierClauseIndex carrierLiteralIndex : Nat)
    (carrierClauseIndexLt : carrierClauseIndex < 2)
    (carrierLiteralIndexLt : carrierLiteralIndex < 2)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directOblique :
      ¬(⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierRoute :=
      (EqualityLink.lensDrawing position link).routes
        carrierClauseIndex carrierLiteralIndex
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierRoute,
        carrierRoute.getLastD (0, 0)⟩
    let directFinal :=
      (⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩ :
        GridSegment).translate
          (EqualityLink.secondCarrierMacroOrigin position link)
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        directFinal.coordinateLower directFinal.coordinateUpper ∨
      carrierFinal.finish = directFinal.finish := by
  exact
    EqualityLink.lensDrawing_second_finalSegmentRectanglesSeparated_or_finish_eq
      geometry ⟨carrierClauseIndex, carrierClauseIndexLt⟩
      ⟨carrierLiteralIndex, carrierLiteralIndexLt⟩
      kind index directOblique

end PeriodicEightOccurrenceSplit
end LeanTrominoes
