/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.ExactOne.PeriodicOneInThreeNoUnitsFigureNineLocalExtendedDirectionCompiler
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineStrictSeparationCheck

/-! # Nonempty finite Figure 9 direction prefixes -/


set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine

open Gadget PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

private theorem normalizedDirections_ne_nil (points : List Cell)
    (orthogonal : OrthogonalPolyline points)
    (different : points.head? ≠ points.getLast?) :
    unitSubdivisionDirections (AxisDirection.normalizeOrthogonalPolyline points) ≠ [] := by
  have nonempty : points ≠ [] := by
    intro empty
    simp [empty] at different
  have normalizedOrthogonal := AxisDirection.normalizeOrthogonalPolyline_orthogonal nonempty orthogonal
  have normalizedDifferent : (AxisDirection.normalizeOrthogonalPolyline points).head? ≠
      (AxisDirection.normalizeOrthogonalPolyline points).getLast? := by
    rw [AxisDirection.normalizeOrthogonalPolyline_head? nonempty orthogonal,
      AxisDirection.normalizeOrthogonalPolyline_getLast? nonempty orthogonal]
    exact different
  cases normalizedEq : AxisDirection.normalizeOrthogonalPolyline points with
  | nil => simp [normalizedEq] at normalizedDifferent
  | cons first rest =>
      cases rest with
      | nil => simp [normalizedEq] at normalizedDifferent
      | cons second rest =>
          rw [normalizedEq] at normalizedOrthogonal
          have positive := AxisDirection.segmentLength_positive_of_axisAligned
            (List.isChain_cons_cons.mp normalizedOrthogonal).1
          intro empty
          have lengthEq := congrArg List.length empty
          simp only [unitSubdivisionDirections, List.length_append,
            List.length_replicate, List.length_nil] at lengthEq
          omega

private def localQueryRoute (query : LocalDirectionQuery) : List Cell :=
  let drawing := templateDrawingOfClauseProfile query.1
  drawing.routeAt (drawing.incidenceAt query.2)

private def extendedQueryRoute (query : LocalDirectionQuery) (direction : AxisDirection)
    (slot : Fin 3) : List Cell :=
  joinAtEndpoint (localQueryRoute query)
    ((⟨0, fun _ => direction⟩ : ComposedClauseExitFanData).extendedRoute slot)

private def endpointCheck (points : List Cell) : Bool :=
  if decide (OrthogonalPolyline points) then decide (points.head? ≠ points.getLast?)
  else decide (unitSubdivisionDirections points ≠ [])

private theorem endpointCheck_sound (points : List Cell) (checked : endpointCheck points = true) :
    unitSubdivisionDirections (AxisDirection.normalizeOrthogonalPolyline points) ≠ [] := by
  by_cases orthogonal : OrthogonalPolyline points
  · have different : points.head? ≠ points.getLast? := by
      simpa [endpointCheck, orthogonal] using checked
    exact normalizedDirections_ne_nil points orthogonal different
  · have different : unitSubdivisionDirections points ≠ [] := by
      simpa [endpointCheck, orthogonal] using checked
    by_cases empty : points = []
    · simp [empty, unitSubdivisionDirections] at different
    · simpa [AxisDirection.normalizeOrthogonalPolyline, empty, orthogonal] using different

/-- Every selected template incidence contains at least one unit edge. -/
theorem normalizedLocalDirectionBlock_ne_nil :
    ∀ query : LocalDirectionQuery, normalizedLocalDirectionBlock query ≠ [] := by
  have checked : (finiteAll fun query : LocalDirectionQuery => endpointCheck (localQueryRoute query)) = true := by
    decide +kernel
  intro query
  exact endpointCheck_sound _ ((finiteAll_eq_true _).mp checked query)

private theorem extendedDirectionBlock_ne_nil :
    ∀ (query : LocalDirectionQuery) (direction : AxisDirection) (slot : Fin 3),
      normalizedLocalExtendedDirectionBlock
        ⟨query.1, query.2, ⟨0, fun _ => direction⟩, slot⟩ ≠ [] := by
  have checked : (finiteAll fun query : LocalDirectionQuery =>
      finiteAll fun direction : AxisDirection => finiteAll fun slot : Fin 3 =>
        endpointCheck (extendedQueryRoute query direction slot)) = true := by
    decide +kernel
  intro query direction slot
  simp only [finiteAll_eq_true] at checked
  exact endpointCheck_sound _ (checked query direction slot)

/-- An extended connector cannot remove the local incidence's first edge.
Only the selected fan direction affects this finite check. -/
theorem normalizedLocalExtendedDirectionBlock_ne_nil
    (query : LocalExtendedDirectionQuery) :
    normalizedLocalExtendedDirectionBlock query ≠ [] := by
  rcases query with ⟨profile, incidence, fan, slot⟩
  simpa only [normalizedLocalExtendedDirectionBlock,
    ComposedClauseExitFanData.extendedRoute, ComposedClauseExitFanData.route]
    using extendedDirectionBlock_ne_nil
      ⟨profile, incidence⟩ (fan.direction slot) slot

end LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine
