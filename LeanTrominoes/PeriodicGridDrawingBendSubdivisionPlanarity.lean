/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionVertexAvoidance

/-! # The straight subdivision of a planar local polygonal drawing is planar -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision

theorem subdivisionDrawing_planar {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (localDrawing : drawing.IsRealLocal source)
    (localGraph : source.IsLocal) {factor : Nat}
    (spacing : 16*(drawing.gridSize:Int)+8 < (factor:Int)) :
    (subdivisionDrawing source drawing factor).IsRealPlanarDrawing (subdivisionGraph source drawing factor) := by
  exact ⟨⟨subdivision_compatible planar localDrawing localGraph spacing,
    subdivisionDrawing_routesSimple planar localDrawing localGraph spacing,
    subdivisionDrawing_verticesAvoidRoutes planar localDrawing localGraph spacing⟩,
    subdivisionDrawing_routesMeetOnlyAtEndpoints planar localDrawing localGraph spacing⟩

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
