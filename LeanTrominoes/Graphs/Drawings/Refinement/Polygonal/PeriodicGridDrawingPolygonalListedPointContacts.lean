/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingPolygonalPointOccurrences
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingPolygonalSegmentContacts
import LeanTrominoes.Common.Geometry.GridPolylineRealListedPointContacts

/-! # A lifted listed bend meets any polygonal piece only at a piece endpoint -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem polygonal_listed_point_segment_contact {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {pointRoute pieceRoute : Nat}
    (pointRouteValid : pointRoute < drawing.edgeRoutes.length)
    (pieceRouteValid : pieceRoute < drawing.edgeRoutes.length) {pointIndex : Nat}
    (pointValid : pointIndex+1 < (drawing.edgeRoute pointRoute).length)
    {piece : GridSegment × Nat}
    (pieceMember : piece ∈ (gridPolylineSegments (drawing.edgeRoute pieceRoute)).zipIdx)
    (pointCell pieceCell : Cell)
    (contains : (piece.1.translate (drawing.periodTranslation pieceCell)).RealContains
      (realCell (Cell.add (drawing.periodTranslation pointCell) (drawing.edgeRoute pointRoute)[pointIndex]))) :
    realCell (Cell.add (drawing.periodTranslation pointCell) (drawing.edgeRoute pointRoute)[pointIndex])=
      realCell (piece.1.translate (drawing.periodTranslation pieceCell)).start ∨
    realCell (Cell.add (drawing.periodTranslation pointCell) (drawing.edgeRoute pointRoute)[pointIndex])=
      realCell (piece.1.translate (drawing.periodTranslation pieceCell)).finish := by
  have pieceRouteMember : drawing.edgeRoute pieceRoute ∈ drawing.edgeRoutes := by
    unfold edgeRoute
    rw [List.getD_eq_getElem _ _ pieceRouteValid]
    exact List.getElem_mem pieceRouteValid
  have simple := (planar.1.2.1 _ pieceRouteMember).translate (drawing.periodTranslation pieceCell)
  have liftedMember := tagged_segment_translate pieceMember (drawing.periodTranslation pieceCell)
  by_cases same : (pointRoute,pointCell)=(pieceRoute,pieceCell)
  · have indexEq : pointRoute=pieceRoute := congrArg Prod.fst same
    have cellEq : pointCell=pieceCell := congrArg Prod.snd same
    subst pointRoute pointCell
    have liftedValid : pointIndex+1 < (translatePolyline (drawing.periodTranslation pieceCell)
        (drawing.edgeRoute pieceRoute)).length := by simpa only [translatePolyline,List.length_map] using pointValid
    have contact := simple.listed_point_segment_contact liftedValid liftedMember
      (by simpa only [translatePolyline,List.getElem_map] using contains)
    simpa only [translatePolyline,List.getElem_map] using contact
  · have pointContains := listed_route_point_contains drawing pointRoute pointIndex pointValid pointCell
    have pieceContains : GridPolyline.RealContains (drawing.realEdgeRoute pieceRoute pieceCell)
        (realCell (Cell.add (drawing.periodTranslation pointCell) (drawing.edgeRoute pointRoute)[pointIndex])) :=
      ⟨_,by simpa only [realEdgeRoute,translatePolyline] using List.fst_mem_of_mem_zipIdx liftedMember,contains⟩
    have endpoint := (planar.2 pointRoute pieceRoute pointCell pieceCell pointRouteValid pieceRouteValid same _
      pointContains pieceContains).2
    exact simple.endpoint_segment_contact liftedMember endpoint contains

end LeanTrominoes.PeriodicGridDrawing
