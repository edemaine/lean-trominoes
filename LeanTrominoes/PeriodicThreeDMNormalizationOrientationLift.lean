import LeanTrominoes.PeriodicThreeDMNormalizationOrientationSites
import LeanTrominoes.PeriodicThreeDMNormalizationWellFormed

/-!
# Infinite-lift provenance for normalized orientation sites

The finite raster stores one representative of every periodic vertex and
route-interior cell, while a drawing orientation is allowed to vary over the
entire infinite lift.  This module connects those two views.  It looks up the
finite provenance of an arbitrary lifted cell and canonically chooses the
geometric period translate of that provenance record represented there.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Look up the finite provenance record underneath an arbitrary cell of the
infinite drawing lift.  Reflecting the drawing row coordinate first returns
to the geometric convention used by normalized routes. -/
def PlanarPresentation.finalOrientationSiteAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (location : Cell) :
    Option FinalOrientationSite :=
  presentation.finalOrientationSites.lookup
    (rasterLocation presentation.finalNormalizationPeriod
      (reflectedLocation location))

/-- Reflection between geometric and drawing-row coordinates is an
involution. -/
@[simp]
theorem reflectedLocation_reflectedLocation (location : Cell) :
    reflectedLocation (reflectedLocation location) = location := by
  rcases location with ⟨horizontal, vertical⟩
  simp [reflectedLocation]

/-- Reading the infinite lift is the finite assignment lookup at the
rasterization of the corresponding geometric point. -/
theorem PlanarPresentation.normalizedOrthogonalDrawing_getAt_eq_finalCellTypeAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (location : Cell) :
    presentation.normalizedOrthogonalDrawing.getAt location =
      presentation.finalCellTypeAt
        (rasterLocation presentation.finalNormalizationPeriod
          (reflectedLocation location)) := by
  unfold PeriodicOrthogonalDrawing.getAt
  rw [presentation.normalizedOrthogonalDrawing_get]
  congr 1
  simpa [PlanarPresentation.normalizedPositionAt] using
    presentation.normalizedPositionAt_values
      (reflectedLocation location)

/-- A successful lifted provenance lookup identifies the local drawing-cell
type at that infinite location. -/
theorem PlanarPresentation.normalizedOrthogonalDrawing_getAt_eq_of_site_lookup
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {location : Cell} {site : FinalOrientationSite}
    (lookup : presentation.finalOrientationSiteAt location = some site) :
    presentation.normalizedOrthogonalDrawing.getAt location =
      site.cellType presentation := by
  rw [presentation.normalizedOrthogonalDrawing_getAt_eq_finalCellTypeAt]
  exact presentation.finalCellTypeAt_eq_of_orientationSite_lookup
    collisionFree lookup

/-- A successful lifted lookup says that the location and its provenance
point have the same finite raster representative. -/
theorem PlanarPresentation.rasterLocation_eq_of_orientationSiteAt
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    {location : Cell} {site : FinalOrientationSite}
    (lookup : presentation.finalOrientationSiteAt location = some site) :
    rasterLocation presentation.finalNormalizationPeriod
        (reflectedLocation location) =
      rasterLocation presentation.finalNormalizationPeriod
        (site.point presentation) := by
  exact presentation.finalOrientationSite_key_eq_point
    (List.mem_of_lookup_eq_some lookup)

/-- Canonically choose the geometric lattice translate represented by an
infinite drawing location and one finite provenance site.  The fallback is
irrelevant when the site was actually obtained by lookup. -/
noncomputable def PlanarPresentation.finalOrientationSiteOccurrenceTranslate
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (location : Cell) (site : FinalOrientationSite) : Cell :=
  if equal :
      rasterLocation presentation.finalNormalizationPeriod
          (reflectedLocation location) =
        rasterLocation presentation.finalNormalizationPeriod
          (site.point presentation) then
    Classical.choose
      ((rasterLocation_eq_iff_exists_periodTranslation
        presentation.finalNormalizationPeriod
        (reflectedLocation location) (site.point presentation)).mp equal)
  else
    (0, 0)

/-- At every successful lookup, the chosen translate reconstructs the exact
geometric occurrence underlying the infinite drawing location. -/
theorem PlanarPresentation.reflectedLocation_eq_orientationSiteOccurrence
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    {location : Cell} {site : FinalOrientationSite}
    (lookup : presentation.finalOrientationSiteAt location = some site) :
    reflectedLocation location =
      Cell.add (site.point presentation)
        (Cell.scale (presentation.finalNormalizationPeriod : Int)
          (presentation.finalOrientationSiteOccurrenceTranslate
            location site)) := by
  have equal := presentation.rasterLocation_eq_of_orientationSiteAt lookup
  unfold PlanarPresentation.finalOrientationSiteOccurrenceTranslate
  simp only [dif_pos equal]
  exact Classical.choose_spec
    ((rasterLocation_eq_iff_exists_periodTranslation
      presentation.finalNormalizationPeriod
      (reflectedLocation location) (site.point presentation)).mp equal)

/-- Positivity of the raster period makes the translate reconstructed from a
successful lookup unique. -/
theorem PlanarPresentation.finalOrientationSiteOccurrenceTranslate_eq
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    {location translate : Cell} {site : FinalOrientationSite}
    (lookup : presentation.finalOrientationSiteAt location = some site)
    (occurrence :
      reflectedLocation location =
        Cell.add (site.point presentation)
          (Cell.scale (presentation.finalNormalizationPeriod : Int)
            translate)) :
    presentation.finalOrientationSiteOccurrenceTranslate location site =
      translate := by
  have selectedOccurrence :=
    presentation.reflectedLocation_eq_orientationSiteOccurrence lookup
  have sumsEqual :
      Cell.add (site.point presentation)
          (Cell.scale (presentation.finalNormalizationPeriod : Int)
            (presentation.finalOrientationSiteOccurrenceTranslate
              location site)) =
        Cell.add (site.point presentation)
          (Cell.scale (presentation.finalNormalizationPeriod : Int)
            translate) :=
    selectedOccurrence.symm.trans occurrence
  apply Cell.scale_injective
    (factor := (presentation.finalNormalizationPeriod : Int))
    (by
      exact_mod_cast
        (Nat.ne_of_gt presentation.finalNormalizationPeriod_pos))
  simp only [Cell.add, Prod.mk.injEq] at sumsEqual
  exact Prod.ext (add_left_cancel sumsEqual.1)
    (add_left_cancel sumsEqual.2)

/-- A listed finite site is recovered at every explicit reflected period
translate of its geometric point. -/
theorem PlanarPresentation.finalOrientationSiteAt_reflected_periodOccurrence
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {storedLocation translate : Cell} {site : FinalOrientationSite}
    (member : (storedLocation, site) ∈
      presentation.finalOrientationSites) :
    presentation.finalOrientationSiteAt
        (reflectedLocation
          (Cell.add (site.point presentation)
            (Cell.scale (presentation.finalNormalizationPeriod : Int)
              translate))) =
      some site := by
  unfold PlanarPresentation.finalOrientationSiteAt
  have keyEqual :
      rasterLocation presentation.finalNormalizationPeriod
          (reflectedLocation
            (reflectedLocation
              (Cell.add (site.point presentation)
                (Cell.scale (presentation.finalNormalizationPeriod : Int)
                  translate)))) =
        storedLocation := by
    rw [reflectedLocation_reflectedLocation]
    calc
      rasterLocation presentation.finalNormalizationPeriod
          (Cell.add (site.point presentation)
            (Cell.scale (presentation.finalNormalizationPeriod : Int)
              translate)) =
          rasterLocation presentation.finalNormalizationPeriod
            (site.point presentation) :=
        rasterLocation_add_period _ _ _
      _ = storedLocation :=
        (presentation.finalOrientationSite_key_eq_point member).symm
  rw [keyEqual]
  exact presentation.finalOrientationSites_lookup_eq_some
    collisionFree member

end PeriodicThreeDM

end LeanTrominoes
