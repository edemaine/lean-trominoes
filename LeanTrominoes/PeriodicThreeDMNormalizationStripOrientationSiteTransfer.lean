/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripOrientationOccurrence

/-!
# Transfer between square and strip orientation provenance
-/

namespace LeanTrominoes

namespace PeriodicThreeDM

/-- Square and strip route provenance enumerate the same site values in the
same recursive order. -/
theorem stripRouteOrientationSites_map_snd_eq_routeOrientationSites
    (period : Nat) (edge : ContractedEdge) :
    ∀ route,
      (stripRouteOrientationSites period edge route).map Prod.snd =
        (routeOrientationSites period edge route).map Prod.snd
  | [] => by simp [stripRouteOrientationSites, routeOrientationSites]
  | [_] => by simp [stripRouteOrientationSites, routeOrientationSites]
  | [_, _] => by simp [stripRouteOrientationSites, routeOrientationSites]
  | before :: current :: after :: rest => by
      simp only [stripRouteOrientationSites, routeOrientationSites,
        List.map_cons]
      exact congrArg (List.cons (.route edge before current after))
        (stripRouteOrientationSites_map_snd_eq_routeOrientationSites
          period edge (current :: after :: rest))

/-- Square and strip provenance lists contain the same site values in the
same vertex-then-route order. -/
theorem PlanarPresentation.finalStripOrientationSites_map_snd_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalStripOrientationSites.map Prod.snd =
      presentation.finalOrientationSites.map Prod.snd := by
  unfold PlanarPresentation.finalStripOrientationSites
    PlanarPresentation.finalOrientationSites
  simp only [List.map_append, List.map_map, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro edge edgeMember
  exact stripRouteOrientationSites_map_snd_eq_routeOrientationSites
    presentation.finalNormalizationPeriod edge
      (presentation.finalNormalizationRoute edge)

/-- Every listed strip provenance site occurs in the square provenance list
with its square-raster key. -/
theorem PlanarPresentation.exists_finalOrientationSite_of_mem_finalStripOrientationSites
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {stripLocation : Cell} {site : FinalOrientationSite}
    (member : (stripLocation, site) ∈
      presentation.finalStripOrientationSites) :
    ∃ squareLocation,
      (squareLocation, site) ∈ presentation.finalOrientationSites := by
  have siteMember : site ∈
      presentation.finalStripOrientationSites.map Prod.snd :=
    List.mem_map.mpr ⟨(stripLocation, site), member, rfl⟩
  rw [presentation.finalStripOrientationSites_map_snd_eq] at siteMember
  rcases List.mem_map.mp siteMember with
    ⟨entry, entryMember, siteEqual⟩
  rcases entry with ⟨squareLocation, squareSite⟩
  change squareSite = site at siteEqual
  subst squareSite
  exact ⟨squareLocation, entryMember⟩

end PeriodicThreeDM
end LeanTrominoes
