/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingUnitSubdivision
import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalRoutes

/-!
# Planarizing canonical orthogonal incidence routes

A canonical orthogonal incidence family already supplies all route-dependent
parts of a positioned periodic CNF drawing: exact graph endpoints and
orthogonality.  The vertex positions, their fundamental-square bounds, and
their distinctness do not depend on which route family is installed.

This file first transfers compatibility from any reference route family with
the same positioned source and placement.  It then unit-subdivides every
orthogonal route and packages the result as a `PlanarIncidencePresentation`.
The planarity proof uses the integer-grid observation that a genuine unit
axis segment contains no integer lattice point in its relative interior.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Pointwise unit subdivision of a positioned incidence-route family. -/
def unitSubdivideIncidenceRoutes
    (routes : IncidenceRoutes) : IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    AxisDirection.unitSubdividePolyline
      (routes clauseIndex literalIndex)

/-- Assembling pointwise subdivided incidence routes is exactly the generic
unit subdivision of the assembled periodic drawing. -/
theorem incidenceDrawing_unitSubdivide
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) :
    incidenceDrawing source placement
        (unitSubdivideIncidenceRoutes routes) =
      (incidenceDrawing source placement routes).unitSubdivide := by
  apply PeriodicGridDrawing.equivData.injective
  simp only [PeriodicGridDrawing.equivData, incidenceDrawing,
    PeriodicGridDrawing.unitSubdivide]
  congr 2
  unfold incidenceEdgeRoutes
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause _
  simp only [List.map_map, Function.comp_def]
  rfl

namespace CanonicalOrthogonalIncidenceRoutes

/-- Route-independent drawing data can be copied from any compatible
reference drawing over the same positioned source and placement. -/
theorem isCompatible_of_reference
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family :
      CanonicalOrthogonalIncidenceRoutes source placement)
    (periodPositive : 0 < placement.period)
    (referenceRoutes : IncidenceRoutes)
    (referenceCompatible :
      (incidenceDrawing source placement
        referenceRoutes).IsCompatible
          source.erase.incidenceGraph) :
    (incidenceDrawing source placement
      family.routes).IsCompatible
        source.erase.incidenceGraph := by
  rcases referenceCompatible with
    ⟨wellFormed, _, _, positionsNodup,
      positionBounds, _⟩
  exact
    ⟨wellFormed,
      incidenceVertexPositions_length source placement,
      incidenceEdgeRoutes_length source family.routes,
      positionsNodup,
      positionBounds,
      family.routesMatch periodPositive⟩

/-- Unit subdivision promotes canonical orthogonal routes to a complete
planar incidence presentation, using a compatible reference family only for
the route-independent vertex geometry. -/
def unitSubdividedPlanarPresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family :
      CanonicalOrthogonalIncidenceRoutes source placement)
    (periodPositive : 0 < placement.period)
    (referenceRoutes : IncidenceRoutes)
    (referenceCompatible :
      (incidenceDrawing source placement
        referenceRoutes).IsCompatible
          source.erase.incidenceGraph) :
    PlanarIncidencePresentation source placement := by
  have compatible :
      (incidenceDrawing source placement
        family.routes).IsCompatible
          source.erase.incidenceGraph :=
    family.isCompatible_of_reference periodPositive
      referenceRoutes referenceCompatible
  have orthogonal :
      (incidenceDrawing source placement
        family.routes).IsOrthogonal :=
    family.isOrthogonal
  exact {
    routes := unitSubdivideIncidenceRoutes family.routes
    periodPositive := periodPositive
    compatible := by
      rw [incidenceDrawing_unitSubdivide]
      exact
        PeriodicGridDrawing.isCompatible_unitSubdivide
          source.erase.incidenceGraph
          (incidenceDrawing source placement family.routes)
          compatible orthogonal
    orthogonal := by
      rw [incidenceDrawing_unitSubdivide]
      exact
        PeriodicGridDrawing.isOrthogonal_unitSubdivide
          (incidenceDrawing source placement family.routes)
          orthogonal
    planar := by
      rw [incidenceDrawing_unitSubdivide]
      exact
        PeriodicGridDrawing.isPlanar_unitSubdivide
          (incidenceDrawing source placement family.routes)
          orthogonal
  }

end CanonicalOrthogonalIncidenceRoutes
end PositionedPeriodicCNF
end LeanTrominoes
