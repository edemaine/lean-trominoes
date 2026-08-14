/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationOrientationSites
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentLookup

/-!
# Orientation provenance for normalized 3DM strip sites
-/

namespace LeanTrominoes

namespace PeriodicThreeDM

/-- Route-interior provenance parallel to the rectangular strip route
rasterizer. -/
def stripRouteOrientationSites (period : Nat) (edge : ContractedEdge) :
    List Cell → List (Cell × FinalOrientationSite)
  | before :: current :: after :: rest =>
      (stripRasterLocation period current,
        .route edge before current after) ::
      stripRouteOrientationSites period edge (current :: after :: rest)
  | _ => []
termination_by points => points.length

/-- Erasing strip route provenance gives the ordinary strip route
assignments. -/
theorem stripRouteOrientationSites_map_cellType
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    ∀ route,
      (stripRouteOrientationSites presentation.finalNormalizationPeriod
          edge route).map
          (fun entry => (entry.1, entry.2.cellType presentation)) =
        stripRouteInteriorAssignments presentation.finalNormalizationPeriod
          edge.color route
  | [] => by
      simp [stripRouteOrientationSites, stripRouteInteriorAssignments]
  | [only] => by
      simp [stripRouteOrientationSites, stripRouteInteriorAssignments]
  | [first, second] => by
      simp [stripRouteOrientationSites, stripRouteInteriorAssignments]
  | before :: current :: after :: rest => by
      simp only [stripRouteOrientationSites, stripRouteInteriorAssignments,
        List.map_cons, FinalOrientationSite.cellType]
      congr 1
      exact stripRouteOrientationSites_map_cellType presentation edge
        (current :: after :: rest)

/-- Every strip route-site key is the rectangular rasterization of the
geometric point in its provenance. -/
theorem stripRouteOrientationSites_key_eq_point
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    ∀ route {location : Cell} {site : FinalOrientationSite},
      (location, site) ∈
          stripRouteOrientationSites presentation.finalNormalizationPeriod
            edge route →
        location = stripRasterLocation presentation.finalNormalizationPeriod
          (site.point presentation)
  | [], _, _, member => by
      simp [stripRouteOrientationSites] at member
  | [_], _, _, member => by
      simp [stripRouteOrientationSites] at member
  | [_, _], _, _, member => by
      simp [stripRouteOrientationSites] at member
  | before :: current :: after :: rest, location, site, member => by
      simp only [stripRouteOrientationSites, List.mem_cons] at member
      rcases member with member | member
      · injection member with locationEq siteEq
        subst location
        subst site
        rfl
      · exact stripRouteOrientationSites_key_eq_point presentation edge
          (current :: after :: rest) member

/-- Complete strip provenance in vertex-before-route lookup order. -/
def PlanarPresentation.finalStripOrientationSites
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List (Cell × FinalOrientationSite) :=
  (problem.contractedGraph.vertices.map fun vertex =>
      (stripRasterLocation presentation.finalNormalizationPeriod
        (presentation.finalNormalizationPosition vertex),
        FinalOrientationSite.vertex vertex)) ++
    (problem.contractedEdges.flatMap fun edge =>
      stripRouteOrientationSites presentation.finalNormalizationPeriod edge
        (presentation.finalNormalizationRoute edge))

/-- Erasing strip provenance recovers the exact strip assignment list. -/
theorem PlanarPresentation.finalStripOrientationSites_map_cellType
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalStripOrientationSites.map
        (fun entry => (entry.1, entry.2.cellType presentation)) =
      presentation.finalStripCellAssignments := by
  unfold PlanarPresentation.finalStripOrientationSites
    PlanarPresentation.finalStripCellAssignments
    PlanarPresentation.finalStripVertexAssignments
    PlanarPresentation.finalStripRouteAssignments
  rw [List.map_append, List.map_map, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro edge edgeMember
  exact stripRouteOrientationSites_map_cellType presentation edge
    (presentation.finalNormalizationRoute edge)

/-- Every complete strip provenance record carries the geometric point whose
rectangular rasterization produced its key. -/
theorem PlanarPresentation.finalStripOrientationSite_key_eq_point
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {location : Cell} {site : FinalOrientationSite}
    (member : (location, site) ∈ presentation.finalStripOrientationSites) :
    location = stripRasterLocation presentation.finalNormalizationPeriod
      (site.point presentation) := by
  unfold PlanarPresentation.finalStripOrientationSites at member
  simp only [List.mem_append] at member
  rcases member with vertexMember | routeMember
  · simp only [List.mem_map] at vertexMember
    rcases vertexMember with ⟨vertex, vertexListMember, equality⟩
    injection equality with locationEq siteEq
    subst location
    subst site
    rfl
  · simp only [List.mem_flatMap] at routeMember
    rcases routeMember with ⟨edge, edgeMember, siteMember⟩
    exact stripRouteOrientationSites_key_eq_point presentation edge
      (presentation.finalNormalizationRoute edge) siteMember

/-- Strip provenance and cell assignments have the same lookup keys. -/
theorem PlanarPresentation.finalStripOrientationSiteLocations_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalStripOrientationSites.map Prod.fst =
      presentation.finalStripAssignmentLocations := by
  unfold PlanarPresentation.finalStripAssignmentLocations
  rw [← presentation.finalStripOrientationSites_map_cellType]
  simp [List.map_map, Function.comp_def]

/-- Strip assignment collision freedom makes provenance lookup
unambiguous. -/
theorem PlanarPresentation.finalStripOrientationSites_nodup_keys
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree) :
    (presentation.finalStripOrientationSites.map Prod.fst).Nodup := by
  rw [presentation.finalStripOrientationSiteLocations_eq]
  exact collisionFree

/-- Every listed strip provenance record is recovered by key lookup. -/
theorem PlanarPresentation.finalStripOrientationSites_lookup_eq_some
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree)
    {location : Cell} {site : FinalOrientationSite}
    (member : (location, site) ∈ presentation.finalStripOrientationSites) :
    presentation.finalStripOrientationSites.lookup location = some site :=
  List.lookup_eq_some_of_mem_of_nodup_keys member
    (presentation.finalStripOrientationSites_nodup_keys collisionFree)

/-- Successful strip provenance lookup erases to the same cell type returned
by the strip cell lookup. -/
theorem PlanarPresentation.finalStripCellTypeAt_eq_of_orientationSite_lookup
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree)
    {location : Cell} {site : FinalOrientationSite}
    (lookup :
      presentation.finalStripOrientationSites.lookup location = some site) :
    presentation.finalStripCellTypeAt location =
      site.cellType presentation := by
  have siteMember := List.mem_of_lookup_eq_some lookup
  have assignmentMember :
      (location, site.cellType presentation) ∈
        presentation.finalStripCellAssignments := by
    rw [← presentation.finalStripOrientationSites_map_cellType]
    exact List.mem_map.mpr ⟨(location, site), siteMember, rfl⟩
  exact presentation.finalStripCellTypeAt_eq_of_mem
    collisionFree assignmentMember

end PeriodicThreeDM
end LeanTrominoes
