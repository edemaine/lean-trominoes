/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationOrientationLift
import LeanTrominoes.PeriodicThreeDMNormalizationStripOrientationSites
import LeanTrominoes.PeriodicThreeDMNormalizationStripReadback

/-!
# Infinite-lift lookup for normalized 3DM strip orientation sites
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Canonical finite representative of an arbitrary location in the
infinite lift of the rectangular strip. -/
def PlanarPresentation.stripFiniteLocation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (location : Cell) : Cell :=
  let position := presentation.stripNormalizedOrthogonalDrawing.positionAt location
  ((position.1.val : Int), (position.2.val : Int))

/-- Look up strip provenance underneath an arbitrary infinite-lift cell. -/
def PlanarPresentation.finalStripOrientationSiteAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (location : Cell) :
    Option FinalOrientationSite :=
  presentation.finalStripOrientationSites.lookup
    (presentation.stripFiniteLocation location)

/-- Reading the infinite strip lift is direct lookup at its canonical finite
representative. -/
theorem PlanarPresentation.stripNormalizedOrthogonalDrawing_getAt_eq_finalStripCellTypeAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (location : Cell) :
    presentation.stripNormalizedOrthogonalDrawing.getAt location =
      presentation.finalStripCellTypeAt
        (presentation.stripFiniteLocation location) := by
  unfold PeriodicOrthogonalDrawing.getAt
  rw [presentation.stripNormalizedOrthogonalDrawing_get]
  rfl

/-- Successful lifted strip provenance identifies the local cell type. -/
theorem PlanarPresentation.stripNormalizedOrthogonalDrawing_getAt_eq_of_site_lookup
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree)
    {location : Cell} {site : FinalOrientationSite}
    (lookup : presentation.finalStripOrientationSiteAt location = some site) :
    presentation.stripNormalizedOrthogonalDrawing.getAt location =
      site.cellType presentation := by
  rw [presentation.stripNormalizedOrthogonalDrawing_getAt_eq_finalStripCellTypeAt]
  exact presentation.finalStripCellTypeAt_eq_of_orientationSite_lookup
    collisionFree lookup

/-- Failed lifted strip provenance lookup means the compiled cell is blank. -/
theorem PlanarPresentation.stripNormalizedOrthogonalDrawing_getAt_eq_blank_of_site_none
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    {location : Cell}
    (lookup : presentation.finalStripOrientationSiteAt location = none) :
    presentation.stripNormalizedOrthogonalDrawing.getAt location = .blank := by
  rw [presentation.stripNormalizedOrthogonalDrawing_getAt_eq_finalStripCellTypeAt]
  unfold PlanarPresentation.finalStripOrientationSiteAt at lookup
  unfold PlanarPresentation.finalStripCellTypeAt
  rw [← presentation.finalStripOrientationSites_map_cellType]
  have mappedLookup :
      (presentation.finalStripOrientationSites.map fun entry =>
        (entry.1, entry.2.cellType presentation)).lookup
          (presentation.stripFiniteLocation location) = none := by
    exact List.lookup_map_value_eq_none
      presentation.finalStripOrientationSites _
        (FinalOrientationSite.cellType presentation) lookup
  rw [mappedLookup]
  rfl

/-- Successful lifted strip lookup equates the finite representative with
the provenance point's rectangular raster key. -/
theorem PlanarPresentation.stripFiniteLocation_eq_of_orientationSiteAt
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    {location : Cell} {site : FinalOrientationSite}
    (lookup : presentation.finalStripOrientationSiteAt location = some site) :
    presentation.stripFiniteLocation location =
      stripRasterLocation presentation.finalNormalizationPeriod
        (site.point presentation) := by
  exact presentation.finalStripOrientationSite_key_eq_point
    (List.mem_of_lookup_eq_some lookup)

end PeriodicThreeDM
end LeanTrominoes
