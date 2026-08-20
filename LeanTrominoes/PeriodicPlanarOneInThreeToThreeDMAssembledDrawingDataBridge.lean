/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalDrawing

/-! # Product data of an assembled periodic 3DM drawing -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem assembledDrawing_equivData
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    PeriodicGridDrawing.equivData (assembledDrawing routing) =
      (routing.period - 1, assembledVertexPositions routing,
        assembledEdgeRoutes routing) := by
  rfl

/-- Fieldwise agreement with an assembled routing identifies the complete
periodic drawing without unfolding the routing implementation. -/
theorem eq_assembledDrawing_of_fields
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (drawing : PeriodicGridDrawing)
    (gridSizePred_eq : drawing.gridSizePred = routing.period - 1)
    (vertexPositions_eq :
      drawing.vertexPositions = assembledVertexPositions routing)
    (edgeRoutes_eq : drawing.edgeRoutes = assembledEdgeRoutes routing) :
    drawing = assembledDrawing routing := by
  apply PeriodicGridDrawing.equivData.injective
  rw [assembledDrawing_equivData]
  change
    (drawing.gridSizePred, drawing.vertexPositions, drawing.edgeRoutes) = _
  exact Prod.ext gridSizePred_eq
    (Prod.ext vertexPositions_eq edgeRoutes_eq)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
