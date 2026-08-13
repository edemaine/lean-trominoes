/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceEscapedSplice
import LeanTrominoes.RetainedAngularFanOuterRouteTranslation

/-!
# Translation covariance of retained source splices

Periodic fallback routes translate their retained source polyline before
reusing the same ordinary or delayed-lane outer fan.  This file records the
structural covariance of tail replacement, whole-polyline retained-ray
rasterization, and both source splice policies.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

/-- Translation commutes with replacement of a polyline head. -/
theorem translatePolyline_replacePolylineHead
    (offset : Cell) (replacement route : List Cell) :
    translatePolyline offset
        (replacePolylineHead replacement route) =
      replacePolylineHead
        (translatePolyline offset replacement)
        (translatePolyline offset route) := by
  unfold replacePolylineHead
  rw [translatePolyline_joinAtEndpoint]
  simp [translatePolyline]

/-- Translation commutes with replacement of a polyline tail. -/
theorem translatePolyline_replacePolylineTail
    (offset : Cell) (route replacement : List Cell) :
    translatePolyline offset
        (replacePolylineTail route replacement) =
      replacePolylineTail
        (translatePolyline offset route)
        (translatePolyline offset replacement) := by
  unfold replacePolylineTail
  rw [show
      translatePolyline offset
          (replacePolylineHead replacement.reverse route.reverse).reverse =
        (translatePolyline offset
          (replacePolylineHead replacement.reverse route.reverse)).reverse by
      simp [translatePolyline]]
  rw [translatePolyline_replacePolylineHead]
  simp [translatePolyline]

namespace PeriodicEightOccurrenceSplit

/-- Translating a segment translates its total retained-ray raster. -/
theorem rasterizeRetainedSegment_translate
    (offset : Cell) (segment : GridSegment) :
    translatePolyline offset (rasterizeRetainedSegment segment) =
      rasterizeRetainedSegment (GridSegment.translate offset segment) := by
  unfold rasterizeRetainedSegment
  have vectorEqual :
      Cell.sub
          (GridSegment.translate offset segment).finish
          (GridSegment.translate offset segment).start =
        Cell.sub segment.finish segment.start := by
    rcases offset with ⟨offsetX, offsetY⟩
    rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
    simp [GridSegment.translate, Cell.add, Cell.sub]
  rw [vectorEqual]
  generalize classified :
      retainedRayClassify
          (Cell.sub segment.finish segment.start) = classifiedRay
  cases classifiedRay with
  | none =>
      simp [translatePolyline, GridSegment.translate]
  | some ray =>
      exact RetainedRay.rasterize_translatePolyline
        ray segment.start offset

/-- Translating every vertex translates the complete retained-ray
rasterization of a polyline. -/
theorem rasterizeRetainedPolyline_translate
    (offset : Cell) (route : List Cell) :
    translatePolyline offset (rasterizeRetainedPolyline route) =
      rasterizeRetainedPolyline (translatePolyline offset route) := by
  induction route using List.twoStepInduction with
  | nil | singleton => simp [translatePolyline]
  | cons_cons first second rest _ tailInduction =>
      rw [rasterizeRetainedPolyline_cons_cons,
        translatePolyline_joinAtEndpoint,
        rasterizeRetainedSegment_translate,
        tailInduction second]
      rfl

/-- Positive or negative integral scaling distributes through cell
translation. -/
private theorem cell_scale_add
    (factor : Int) (offset point : Cell) :
    Cell.scale factor (Cell.add offset point) =
      Cell.add (Cell.scale factor offset) (Cell.scale factor point) := by
  rcases offset with ⟨offsetX, offsetY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.scale, Cell.add]
  constructor <;> ring

/-- Scaling a translated polyline scales its translation vector. -/
theorem scalePolyline_translatePolyline'
    (factor : Int) (offset : Cell) (route : List Cell) :
    scalePolyline factor (translatePolyline offset route) =
      translatePolyline (Cell.scale factor offset)
        (scalePolyline factor route) := by
  unfold scalePolyline translatePolyline
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  exact cell_scale_add factor offset point

/-- On a nonempty polyline, translation commutes with the total final-point
lookup used to position the outer fan. -/
theorem translatePolyline_getLastD
    (offset : Cell) (route : List Cell)
    (routeNonempty : route ≠ []) :
    (translatePolyline offset route).getLastD (0, 0) =
      Cell.add offset (route.getLastD (0, 0)) := by
  let last := route.getLast routeNonempty
  have lastEq : route.getLast? = some last := by
    exact List.getLast?_eq_some_getLast routeNonempty
  have translatedLastEq :
      (translatePolyline offset route).getLast? =
        some (Cell.add offset last) := by
    simpa [translatePolyline, lastEq] using
      congrArg (Option.map (Cell.add offset)) lastEq
  rw [List.getLastD_eq_getLast?, translatedLastEq,
    List.getLastD_eq_getLast?, lastEq]
  simp

/-- Translating an ordinary pre-rasterized source splice by the refined
offset is the splice of the translated retained source route. -/
theorem retainedAngularFanSplicedBoundaryPolyline_translate
    (offset : Cell) (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeNonempty : route ≠ []) :
    translatePolyline
        (Cell.scale retainedTerminalFanTotalRefinement offset)
        (retainedAngularFanSplicedBoundaryPolyline
          route terminal slot) =
      retainedAngularFanSplicedBoundaryPolyline
        (translatePolyline offset route) terminal slot := by
  unfold retainedAngularFanSplicedBoundaryPolyline
  rw [translatePolyline_replacePolylineTail,
    scalePolyline_translatePolyline',
    retainedTerminalFanOuterCompleteRoute_translatePolyline,
    translatePolyline_getLastD offset route routeNonempty,
    cell_scale_add]

/-- Translating an ordinary rasterized source splice by the refined offset
is the rasterized splice of the translated retained source route. -/
theorem retainedAngularFanSplicedBoundaryRoute_translate
    (offset : Cell) (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeNonempty : route ≠ []) :
    translatePolyline
        (Cell.scale retainedTerminalFanTotalRefinement offset)
        (retainedAngularFanSplicedBoundaryRoute
          route terminal slot) =
      retainedAngularFanSplicedBoundaryRoute
        (translatePolyline offset route) terminal slot := by
  unfold retainedAngularFanSplicedBoundaryRoute
  rw [rasterizeRetainedPolyline_translate,
    retainedAngularFanSplicedBoundaryPolyline_translate
      offset route terminal slot routeNonempty]

/-- Translating a delayed-lane pre-rasterized source splice by the refined
offset is the escaped splice of the translated retained source route. -/
theorem retainedAngularFanEscapedSplicedBoundaryPolyline_translate
    (offset : Cell) (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeNonempty : route ≠ []) :
    translatePolyline
        (Cell.scale retainedTerminalFanTotalRefinement offset)
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          route terminal slot) =
      retainedAngularFanEscapedSplicedBoundaryPolyline
        (translatePolyline offset route) terminal slot := by
  unfold retainedAngularFanEscapedSplicedBoundaryPolyline
  rw [translatePolyline_replacePolylineTail,
    scalePolyline_translatePolyline',
    retainedTerminalFanOuterEscapedCompleteRoute_translatePolyline,
    translatePolyline_getLastD offset route routeNonempty,
    cell_scale_add]

/-- Translating a delayed-lane rasterized source splice by the refined
offset is the escaped splice of the translated retained source route. -/
theorem retainedAngularFanEscapedSplicedBoundaryRoute_translate
    (offset : Cell) (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeNonempty : route ≠ []) :
    translatePolyline
        (Cell.scale retainedTerminalFanTotalRefinement offset)
        (retainedAngularFanEscapedSplicedBoundaryRoute
          route terminal slot) =
      retainedAngularFanEscapedSplicedBoundaryRoute
        (translatePolyline offset route) terminal slot := by
  unfold retainedAngularFanEscapedSplicedBoundaryRoute
  rw [rasterizeRetainedPolyline_translate,
    retainedAngularFanEscapedSplicedBoundaryPolyline_translate
      offset route terminal slot routeNonempty]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
