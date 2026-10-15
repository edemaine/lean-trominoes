/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceTailSeparation

/-! Strict separation of a repeated ray using its small linear hull. -/
namespace LeanTrominoes.PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

def retainedRayHullSeparationCheck (ray : RetainedRay) (start : Cell) (cycle : List Cell) : Bool :=
  ([(1, 0), (0, 1), (1, 1), (1, -1)] : List Cell).any fun normal =>
    decide (routeLinearMaximum normal (ray.linearHull start) < routeLinearMinimum normal cycle ∨
      routeLinearMaximum normal cycle < routeLinearMinimum normal (ray.linearHull start))

theorem retainedRayHullSeparationCheck_sound (ray : RetainedRay) (start : Cell) (cycle : List Cell)
    (checked : retainedRayHullSeparationCheck ray start cycle = true) :
    RoutesStrictlyAvoidEachOther (ray.rasterize start) cycle := by
  simp only [retainedRayHullSeparationCheck, List.any_eq_true, decide_eq_true_eq] at checked
  obtain ⟨normal, _, separated⟩ := checked
  let hull := ray.linearHull start
  have bounded (p : Cell) (hp : p ∈ ray.rasterize start) :=
    ray.rasterize_linearBounds_of_hull start normal
      (routeLinearMinimum normal hull) (routeLinearMaximum normal hull)
      (fun p hp => ⟨routeLinearMinimum_le_linearValue normal hull hp,
        linearValue_le_routeLinearMaximum normal hull hp⟩) hp
  rcases separated with before | after
  · exact routesStrictlyAvoidEachOther_of_linear_separated normal (routeLinearMaximum normal hull)
      (fun p hp => (bounded p hp).2)
      (fun p hp => lt_of_lt_of_le before (routeLinearMinimum_le_linearValue normal cycle hp))
  · exact (routesStrictlyAvoidEachOther_of_linear_separated normal (routeLinearMaximum normal cycle)
      (fun p hp => linearValue_le_routeLinearMaximum normal cycle hp)
      (fun p hp => lt_of_lt_of_le after (bounded p hp).1)).symm

end LeanTrominoes.PeriodicEightOccurrenceSplit
