/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripCellAssignmentBounds
import LeanTrominoes.PeriodicThreeDMNormalizationStripOrientationTranslationGeometry

/-!
# Occurrences of normalized 3DM strip orientation sites
-/

namespace LeanTrominoes

namespace PeriodicThreeDM

/-- Erasing a listed strip provenance record produces a member of the strip
assignment list. -/
theorem PlanarPresentation.finalStripOrientationSite_assignment_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {location : Cell} {site : FinalOrientationSite}
    (member : (location, site) ∈ presentation.finalStripOrientationSites) :
    (location, site.cellType presentation) ∈
      presentation.finalStripCellAssignments := by
  rw [← presentation.finalStripOrientationSites_map_cellType]
  exact List.mem_map.mpr ⟨(location, site), member, rfl⟩

/-- Every listed provenance point has an in-range shifted/reflected vertical
coordinate under the strip construction hypotheses. -/
theorem ContinuousPlanarPresentation.finalStripOrientationSite_vertical_bounds
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    {storedLocation : Cell} {site : FinalOrientationSite}
    (member : (storedLocation, site) ∈
      presentation.toPlanarPresentation.finalStripOrientationSites) :
    0 ≤ (stripReflectedLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (site.point presentation.toPlanarPresentation)).2 ∧
      (stripReflectedLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (site.point presentation.toPlanarPresentation)).2 <
        (presentation.toPlanarPresentation.finalStripHeight : Int) := by
  let planar := presentation.toPlanarPresentation
  have assignmentMember :=
    planar.finalStripOrientationSite_assignment_mem member
  have interior :=
    presentation.finalStripCellAssignment_vertical_interior
      wellFormed degree horizontal sourceInside assignmentMember
  have keyEqual := planar.finalStripOrientationSite_key_eq_point member
  have verticalEqual := congrArg Prod.snd keyEqual
  simp only [stripRasterLocation] at verticalEqual
  unfold PlanarPresentation.finalStripHeight
  constructor
  · change 0 ≤ 2 * (planar.finalNormalizationPeriod : Int) -
      (site.point planar).2
    rw [← verticalEqual]
    exact le_of_lt interior.1
  · change 2 * (planar.finalNormalizationPeriod : Int) -
      (site.point planar).2 < 3 * planar.finalNormalizationPeriod + 1
    have upper : storedLocation.2 <
        3 * (planar.finalNormalizationPeriod : Int) + 1 := by
      have periodEqual : planar.finalNormalizationPeriod =
          presentation.toPlanarPresentation.finalNormalizationPeriod := rfl
      rw [periodEqual]
      exact lt_trans interior.2 (by omega)
    rw [← verticalEqual]
    exact upper

/-- Canonically choose the rectangular block translate represented by an
infinite strip location and provenance site. -/
noncomputable def PlanarPresentation.finalStripOrientationSiteOccurrenceTranslate
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (location : Cell) (site : FinalOrientationSite) : Cell := by
  classical
  exact
    if existsTranslate : ∃ translate : Cell,
        location = Cell.add
          (stripReflectedLocation presentation.finalNormalizationPeriod
            (site.point presentation))
          (presentation.stripPeriodTranslation translate) then
      Classical.choose existsTranslate
    else
      (0, 0)

/-- Successful strip provenance lookup reconstructs the exact infinite-lift
occurrence using the selected rectangular block translation. -/
theorem ContinuousPlanarPresentation.location_eq_stripOrientationSiteOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    {location : Cell} {site : FinalOrientationSite}
    (lookup :
      presentation.toPlanarPresentation.finalStripOrientationSiteAt location =
        some site) :
    let planar := presentation.toPlanarPresentation
    location = Cell.add
      (stripReflectedLocation planar.finalNormalizationPeriod
        (site.point planar))
      (planar.stripPeriodTranslation
        (planar.finalStripOrientationSiteOccurrenceTranslate location site)) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  have member := List.mem_of_lookup_eq_some lookup
  have verticalBounds :=
    presentation.finalStripOrientationSite_vertical_bounds
      wellFormed degree horizontal sourceInside member
  have finiteEqual := planar.stripFiniteLocation_eq_of_orientationSiteAt lookup
  have existsTranslate := planar.exists_stripPeriodTranslation_of_finite_eq
    location (site.point planar) verticalBounds finiteEqual
  classical
  unfold PlanarPresentation.finalStripOrientationSiteOccurrenceTranslate
  rw [dif_pos existsTranslate]
  exact Classical.choose_spec existsTranslate

/-- The selected strip occurrence translate is unique. -/
theorem ContinuousPlanarPresentation.finalStripOrientationSiteOccurrenceTranslate_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    {location translate : Cell} {site : FinalOrientationSite}
    (lookup :
      presentation.toPlanarPresentation.finalStripOrientationSiteAt location =
        some site)
    (occurrence :
      let planar := presentation.toPlanarPresentation
      location = Cell.add
        (stripReflectedLocation planar.finalNormalizationPeriod
          (site.point planar))
        (planar.stripPeriodTranslation translate)) :
    presentation.toPlanarPresentation.finalStripOrientationSiteOccurrenceTranslate
        location site = translate := by
  let planar := presentation.toPlanarPresentation
  have selectedOccurrence :=
    presentation.location_eq_stripOrientationSiteOccurrence
      wellFormed degree horizontal sourceInside lookup
  have translationsEqual :
      planar.stripPeriodTranslation
          (planar.finalStripOrientationSiteOccurrenceTranslate location site) =
        planar.stripPeriodTranslation translate := by
    have sumsEqual := selectedOccurrence.symm.trans occurrence
    rcases stripReflectedLocation planar.finalNormalizationPeriod
      (site.point planar) with ⟨baseX, baseY⟩
    simpa only [Cell.add, Prod.mk.injEq] using
      Prod.ext (add_left_cancel (congrArg Prod.fst sumsEqual))
        (add_left_cancel (congrArg Prod.snd sumsEqual))
  exact planar.stripPeriodTranslation_injective translationsEqual

/-- Every explicit rectangular-period occurrence of a listed site is
recovered by infinite-lift provenance lookup. -/
theorem ContinuousPlanarPresentation.finalStripOrientationSiteAt_periodOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    {storedLocation translate : Cell} {site : FinalOrientationSite}
    (member : (storedLocation, site) ∈
      presentation.toPlanarPresentation.finalStripOrientationSites) :
    let planar := presentation.toPlanarPresentation
    planar.finalStripOrientationSiteAt
        (Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod
            (site.point planar))
          (planar.stripPeriodTranslation translate)) =
      some site := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  unfold PlanarPresentation.finalStripOrientationSiteAt
  have verticalBounds :=
    presentation.finalStripOrientationSite_vertical_bounds
      wellFormed degree horizontal sourceInside member
  have keyEqual :
      planar.stripFiniteLocation
          (Cell.add
            (stripReflectedLocation planar.finalNormalizationPeriod
              (site.point planar))
            (planar.stripPeriodTranslation translate)) = storedLocation := by
    calc
      _ = stripRasterLocation planar.finalNormalizationPeriod
          (site.point planar) :=
        planar.stripFiniteLocation_add_stripPeriodTranslation
          (site.point planar) translate verticalBounds
      _ = storedLocation :=
        (planar.finalStripOrientationSite_key_eq_point member).symm
  rw [keyEqual]
  exact planar.finalStripOrientationSites_lookup_eq_some
    collisionFree member

end PeriodicThreeDM
end LeanTrominoes
