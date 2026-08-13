/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationMagnifiedContacts
import LeanTrominoes.PeriodicThreeDMVertexNormalizationRouteValidity

/-!
# Intermediate drawings for degree-three vertex normalization

The executable normalization data names routes after each of the three
local replacement rounds.  This module packages the first two boundaries
as periodic grid drawings.  Each boundary is obtained from the affine
unit-refinement of the preceding drawing by replacing its stored routes
with the corresponding locally spliced routes.

Keeping these intermediate drawings explicit lets geometric invariants be
proved one round at a time and then reused by the following round.
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Stored routes after the direction-normalizing replacement, in
contracted-edge presentation order. -/
def PlanarPresentation.normalizationEdgeRoutes1
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : List (List Cell) :=
  problem.contractedEdges.zipIdx.map fun tagged =>
    presentation.normalizationRoute1 tagged.1

/-- The periodic drawing after the first local endpoint-template round. -/
def PlanarPresentation.normalizationGridDrawing1
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : PeriodicGridDrawing :=
  { vertexNormalizationMagnifiedUnitDrawing
      presentation.contractedDrawing with
    edgeRoutes := presentation.normalizationEdgeRoutes1 }

/-- Stored routes after the first cyclic-rotation replacement, in
contracted-edge presentation order. -/
def PlanarPresentation.normalizationEdgeRoutes2
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : List (List Cell) :=
  problem.contractedEdges.zipIdx.map fun tagged =>
    presentation.normalizationRoute2 tagged.1

/-- The periodic drawing after the second local endpoint-template round. -/
def PlanarPresentation.normalizationGridDrawing2
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : PeriodicGridDrawing :=
  { vertexNormalizationMagnifiedUnitDrawing
      presentation.normalizationGridDrawing1 with
    edgeRoutes := presentation.normalizationEdgeRoutes2 }

@[simp]
theorem PlanarPresentation.normalizationGridDrawing1_gridSize
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.normalizationGridDrawing1.gridSize =
      12 * presentation.contractedDrawing.gridSize := by
  change
    (vertexNormalizationMagnifiedUnitDrawing
      presentation.contractedDrawing).gridSize = _
  exact vertexNormalizationMagnifiedUnitDrawing_gridSize _

@[simp]
theorem PlanarPresentation.normalizationGridDrawing2_gridSize
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.normalizationGridDrawing2.gridSize =
      12 * presentation.normalizationGridDrawing1.gridSize := by
  change
    (vertexNormalizationMagnifiedUnitDrawing
      presentation.normalizationGridDrawing1).gridSize = _
  exact vertexNormalizationMagnifiedUnitDrawing_gridSize _

@[simp]
theorem PlanarPresentation.normalizationGridDrawing1_vertexPositions
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.normalizationGridDrawing1.vertexPositions =
      presentation.contractedDrawing.vertexPositions.map
        normalizeVertexPosition := by
  simp [PlanarPresentation.normalizationGridDrawing1,
    vertexNormalizationMagnifiedUnitDrawing_vertexPositions]

@[simp]
theorem PlanarPresentation.normalizationGridDrawing2_vertexPositions
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.normalizationGridDrawing2.vertexPositions =
      presentation.normalizationGridDrawing1.vertexPositions.map
        normalizeVertexPosition := by
  simp [PlanarPresentation.normalizationGridDrawing2,
    vertexNormalizationMagnifiedUnitDrawing_vertexPositions]

@[simp]
theorem PlanarPresentation.normalizationGridDrawing1_edgeRoutes
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.normalizationGridDrawing1.edgeRoutes =
      presentation.normalizationEdgeRoutes1 := by
  rfl

@[simp]
theorem PlanarPresentation.normalizationGridDrawing2_edgeRoutes
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.normalizationGridDrawing2.edgeRoutes =
      presentation.normalizationEdgeRoutes2 := by
  rfl

/-- Indexed edge lookup at the first stage recovers its executable route. -/
theorem PlanarPresentation.normalizationGridDrawing1_edgeRoute
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tagged : ContractedEdge × Nat}
    (member : tagged ∈ problem.contractedEdges.zipIdx) :
    presentation.normalizationGridDrawing1.edgeRoute tagged.2 =
      presentation.normalizationRoute1 tagged.1 := by
  unfold PeriodicGridDrawing.edgeRoute
    PlanarPresentation.normalizationGridDrawing1
    PlanarPresentation.normalizationEdgeRoutes1
  exact PeriodicOrthocrossing.getD_map_zipIdx_of_mem
    problem.contractedEdges
    (fun tagged => presentation.normalizationRoute1 tagged.1)
    [] member

/-- Indexed edge lookup at the second stage recovers its executable route. -/
theorem PlanarPresentation.normalizationGridDrawing2_edgeRoute
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tagged : ContractedEdge × Nat}
    (member : tagged ∈ problem.contractedEdges.zipIdx) :
    presentation.normalizationGridDrawing2.edgeRoute tagged.2 =
      presentation.normalizationRoute2 tagged.1 := by
  unfold PeriodicGridDrawing.edgeRoute
    PlanarPresentation.normalizationGridDrawing2
    PlanarPresentation.normalizationEdgeRoutes2
  exact PeriodicOrthocrossing.getD_map_zipIdx_of_mem
    problem.contractedEdges
    (fun tagged => presentation.normalizationRoute2 tagged.1)
    [] member

end PeriodicThreeDM
end LeanTrominoes
