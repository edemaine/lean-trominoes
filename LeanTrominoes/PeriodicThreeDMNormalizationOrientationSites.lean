import LeanTrominoes.PeriodicThreeDMContractedTagEndpoints
import LeanTrominoes.PeriodicThreeDMNormalizationFinalAssignmentCollisionFreedom

/-!
# Orientation metadata for normalized raster sites

The cell rasterizer deliberately stores only `OrthogonalCellType`s.  Semantic
transport also needs to remember which contracted vertex or displayed route
triple produced each nonblank site.  This module defines a parallel metadata
list and proves that erasing its provenance gives exactly the existing final
cell-assignment list, in the same lookup order.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Provenance of one nonblank normalized raster cell. -/
inductive FinalOrientationSite
  | vertex (vertex : PeriodicThreeDMVertex)
  | route (edge : ContractedEdge) (before current after : Cell)
  deriving DecidableEq, Repr

namespace FinalOrientationSite

/-- The geometric point occupied by a provenance record. -/
def point
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    FinalOrientationSite → Cell
  | .vertex v => presentation.finalNormalizationPosition v
  | .route _ _ current _ => current

/-- Erase provenance to the cell type emitted by the rasterizer. -/
def cellType
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    FinalOrientationSite → OrthogonalCellType
  | .vertex v => presentation.finalVertexCellType v
  | .route edge before current after =>
      routingCellTypeAt before current after edge.color

end FinalOrientationSite

/-- Route-interior metadata parallel to `routeInteriorAssignments`. -/
def routeOrientationSites (period : Nat) (edge : ContractedEdge) :
    List Cell → List (Cell × FinalOrientationSite)
  | before :: current :: after :: rest =>
      (rasterLocation period current,
        .route edge before current after) ::
      routeOrientationSites period edge (current :: after :: rest)
  | _ => []
termination_by points => points.length

/-- Erasing route provenance gives exactly the ordinary route rasterizer. -/
theorem routeOrientationSites_map_cellType
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    ∀ route,
      (routeOrientationSites presentation.finalNormalizationPeriod edge route).map
          (fun entry => (entry.1, entry.2.cellType presentation)) =
        routeInteriorAssignments presentation.finalNormalizationPeriod
          edge.color route
  | [] => by
      simp [routeOrientationSites, routeInteriorAssignments]
  | [only] => by
      simp [routeOrientationSites, routeInteriorAssignments]
  | [first, second] => by
      simp [routeOrientationSites, routeInteriorAssignments]
  | before :: current :: after :: rest => by
      simp only [routeOrientationSites, routeInteriorAssignments, List.map_cons,
        FinalOrientationSite.cellType]
      congr 1
      exact routeOrientationSites_map_cellType presentation edge
        (current :: after :: rest)

/-- Every route-site key is the rasterization of the geometric point stored
in its provenance record. -/
theorem routeOrientationSites_key_eq_point
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    ∀ route {location : Cell} {site : FinalOrientationSite},
      (location, site) ∈
          routeOrientationSites presentation.finalNormalizationPeriod
            edge route →
        location = rasterLocation presentation.finalNormalizationPeriod
          (site.point presentation)
  | [], _, _, member => by
      simp [routeOrientationSites] at member
  | [_], _, _, member => by
      simp [routeOrientationSites] at member
  | [_, _], _, _, member => by
      simp [routeOrientationSites] at member
  | before :: current :: after :: rest, location, site, member => by
      simp only [routeOrientationSites, List.mem_cons] at member
      rcases member with member | member
      · injection member with locationEq siteEq
        subst location
        subst site
        rfl
      · exact routeOrientationSites_key_eq_point presentation edge
          (current :: after :: rest) member

/-- Complete provenance list in the same vertex-before-route lookup order as
`finalCellAssignments`. -/
def PlanarPresentation.finalOrientationSites
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List (Cell × FinalOrientationSite) :=
  (problem.contractedGraph.vertices.map fun vertex =>
      (rasterLocation presentation.finalNormalizationPeriod
        (presentation.finalNormalizationPosition vertex),
        FinalOrientationSite.vertex vertex)) ++
    (problem.contractedEdges.flatMap fun edge =>
      routeOrientationSites presentation.finalNormalizationPeriod edge
        (presentation.finalNormalizationRoute edge))

/-- Provenance erasure is extensionally the existing final assignment list. -/
theorem PlanarPresentation.finalOrientationSites_map_cellType
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalOrientationSites.map
        (fun entry => (entry.1, entry.2.cellType presentation)) =
      presentation.finalCellAssignments := by
  unfold PlanarPresentation.finalOrientationSites
    PlanarPresentation.finalCellAssignments
    PlanarPresentation.finalVertexAssignments
    PlanarPresentation.finalRouteAssignments
  rw [List.map_append, List.map_map, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro edge edgeMember
  exact routeOrientationSites_map_cellType presentation edge
    (presentation.finalNormalizationRoute edge)

/-- Every complete provenance record carries precisely the geometric point
whose rasterization produced its stored lookup key. -/
theorem PlanarPresentation.finalOrientationSite_key_eq_point
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {location : Cell} {site : FinalOrientationSite}
    (member : (location, site) ∈ presentation.finalOrientationSites) :
    location = rasterLocation presentation.finalNormalizationPeriod
      (site.point presentation) := by
  unfold PlanarPresentation.finalOrientationSites at member
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
    exact routeOrientationSites_key_eq_point presentation edge
      (presentation.finalNormalizationRoute edge) siteMember

/-- Provenance and cell assignments have exactly the same location keys. -/
theorem PlanarPresentation.finalOrientationSiteLocations_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalOrientationSites.map Prod.fst =
      presentation.finalAssignmentLocations := by
  unfold PlanarPresentation.finalAssignmentLocations
  rw [← presentation.finalOrientationSites_map_cellType]
  simp [List.map_map, Function.comp_def]

/-- Collision freedom therefore makes the provenance lookup unambiguous. -/
theorem PlanarPresentation.finalOrientationSites_nodup_keys
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree) :
    (presentation.finalOrientationSites.map Prod.fst).Nodup := by
  rw [presentation.finalOrientationSiteLocations_eq]
  exact collisionFree

/-- Every listed provenance record is recovered by location lookup. -/
theorem PlanarPresentation.finalOrientationSites_lookup_eq_some
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {location : Cell} {site : FinalOrientationSite}
    (member : (location, site) ∈ presentation.finalOrientationSites) :
    presentation.finalOrientationSites.lookup location = some site :=
  List.lookup_eq_some_of_mem_of_nodup_keys member
    (presentation.finalOrientationSites_nodup_keys collisionFree)

/-- Successful provenance lookup erases to the same cell type returned by the
ordinary final lookup. -/
theorem PlanarPresentation.finalCellTypeAt_eq_of_orientationSite_lookup
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {location : Cell} {site : FinalOrientationSite}
    (lookup : presentation.finalOrientationSites.lookup location = some site) :
    presentation.finalCellTypeAt location = site.cellType presentation := by
  have siteMember := List.mem_of_lookup_eq_some lookup
  have assignmentMember :
      (location, site.cellType presentation) ∈
        presentation.finalCellAssignments := by
    rw [← presentation.finalOrientationSites_map_cellType]
    exact List.mem_map.mpr ⟨(location, site), siteMember, rfl⟩
  exact presentation.finalCellTypeAt_eq_of_mem collisionFree assignmentMember

end PeriodicThreeDM

end LeanTrominoes
