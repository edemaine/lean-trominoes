/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionJoin
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequests

/-! # Incidence decomposition of contracted-edge direction requests -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open Gadget PeriodicOrthocrossing NormalizationCompiler

/-- A retained contracted edge uses exactly its represented incidence-route
direction word. -/
@[simp] theorem ofEdge_retained_directions
    (input : NormalizationCompiler.Input)
    (color : WireColor) (atom : Nat) (incidence : Incidence) :
    (ofEdge input (.retained color atom incidence)).directions =
      unitSubdivisionDirections
        (incidenceRoute input ⟨incidence.tripleIndex, color⟩) := by
  rfl

/-- Translation disappears from the reversed incidence suffix used by a
degree-two contracted edge. -/
theorem unitSubdivisionDirections_reversedIncidenceRouteAt
    (input : NormalizationCompiler.Input)
    (color : WireColor) (first second : Incidence) :
    unitSubdivisionDirections
        (reversedIncidenceRouteAt input color first second) =
      unitSubdivisionDirections
        (incidenceRoute input ⟨second.tripleIndex, color⟩).reverse := by
  unfold reversedIncidenceRouteAt
  rw [show
      (translatePolyline
          (input.drawing.periodTranslation
            (Cell.sub first.offset second.offset))
          (incidenceRoute input
            ⟨second.tripleIndex, color⟩)).reverse =
        translatePolyline
          (input.drawing.periodTranslation
            (Cell.sub first.offset second.offset))
          (incidenceRoute input
            ⟨second.tripleIndex, color⟩).reverse by
    simp [translatePolyline]]
  exact unitSubdivisionDirections_translatePolyline _ _

/-- Under the standard nondegenerate common-boundary conditions, a
degree-two through edge's initial word is the first incidence followed by
the reversed second incidence.  Thus no contracted polyline needs to be
materialized by the source emitter. -/
theorem ofEdge_through_directions
    (input : NormalizationCompiler.Input)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (firstLength :
      2 ≤ (incidenceRoute input
        ⟨first.tripleIndex, color⟩).length)
    (boundary :
      (incidenceRoute input
          ⟨first.tripleIndex, color⟩).getLast? =
        (reversedIncidenceRouteAt input color first second).head?) :
    (ofEdge input (.through color atom first second)).directions =
      unitSubdivisionDirections
          (incidenceRoute input ⟨first.tripleIndex, color⟩) ++
        unitSubdivisionDirections
          (incidenceRoute input
            ⟨second.tripleIndex, color⟩).reverse := by
  change
    unitSubdivisionDirections
        (joinPolylines
          (incidenceRoute input ⟨first.tripleIndex, color⟩)
          (reversedIncidenceRouteAt input color first second)) = _
  rw [unitSubdivisionDirections_joinPolylines firstLength boundary,
    unitSubdivisionDirections_reversedIncidenceRouteAt]

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
