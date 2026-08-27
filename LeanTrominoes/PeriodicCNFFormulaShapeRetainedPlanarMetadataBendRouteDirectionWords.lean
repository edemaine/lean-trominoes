/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRouteDirections
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation

/-! # Complete direction words of retained bend-corner routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The complete unit-step direction word of one route in the finite corner
equality table. -/
def bendRouteDirections
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
    (cornerEqualityRoutes firstPort secondPort
      localClauseIndex literalIndex)

/-- Placing and scoping a bend translates its fixed corner route, so its
complete unit-step direction word remains the finite table word. -/
theorem bend_routeDirections_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (localClauseIndex literalIndex : Nat) :
    Gadget.unitSubdivisionDirections
        (((DrawingPlanarSATClauseSource.bend
            routeBend localClauseIndex).incidenceDrawing source).routes
          localClauseIndex literalIndex) =
      bendRouteDirections routeBend.incomingPort routeBend.outgoingPort
        localClauseIndex literalIndex := by
  change Gadget.unitSubdivisionDirections
      ((cornerEqualityRoutes routeBend.incomingPort routeBend.outgoingPort
        localClauseIndex literalIndex).map
          (Cell.add (Cell.scale planarMacroScale
            (routeBend.drawingPoint source.incidenceGraph)))) = _
  change Gadget.unitSubdivisionDirections
      (PeriodicOrthocrossing.translatePolyline
        (Cell.scale planarMacroScale
          (routeBend.drawingPoint source.incidenceGraph))
        (cornerEqualityRoutes routeBend.incomingPort routeBend.outgoingPort
          localClauseIndex literalIndex)) = _
  exact Gadget.unitSubdivisionDirections_translatePolyline _ _

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
