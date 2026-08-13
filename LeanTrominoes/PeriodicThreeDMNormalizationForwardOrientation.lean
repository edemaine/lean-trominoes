/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationVertexOrientation

/-!
# Forward orientation on the normalized drawing

A suppressed 3DM orientation assigns one inward value to each contracted
endpoint.  Along a routed edge, every internal cell points backward with the
negation of the source-end value and forward with the source-end value.  This
module packages those values into an orientation of the infinite normalized
drawing and proves all local cell constraints.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Membership in route provenance recovers the displayed consecutive
three-point window and confirms the edge stored in the site. -/
theorem exists_route_triple_of_mem_routeOrientationSites
    (period : Nat) (owner : ContractedEdge) :
    ∀ {route : List Cell} {location : Cell}
      {storedEdge : ContractedEdge} {before current after : Cell},
      (location, FinalOrientationSite.route storedEdge before current after) ∈
          routeOrientationSites period owner route →
        owner = storedEdge ∧
          ∃ leading rest,
            route = leading ++ before :: current :: after :: rest
  | [], _, _, _, _, _, member => by
      simp [routeOrientationSites] at member
  | [_], _, _, _, _, _, member => by
      simp [routeOrientationSites] at member
  | [_, _], _, _, _, _, _, member => by
      simp [routeOrientationSites] at member
  | routeBefore :: routeCurrent :: routeAfter :: routeRest,
      location, storedEdge, before, current, after, member => by
      simp only [routeOrientationSites, List.mem_cons] at member
      rcases member with equal | tailMember
      · cases equal
        exact ⟨rfl, [], routeRest, by simp⟩
      · rcases exists_route_triple_of_mem_routeOrientationSites
          period owner tailMember with
        ⟨edgeEq, leading, rest, routeEq⟩
        exact ⟨edgeEq, routeBefore :: leading, rest, by simp [routeEq]⟩

/-- Route provenance never contains a vertex site. -/
theorem not_mem_vertex_routeOrientationSites
    (period : Nat) (edge : ContractedEdge) :
    ∀ (route : List Cell) (location : Cell)
      (vertex : PeriodicThreeDMVertex),
      (location, FinalOrientationSite.vertex vertex) ∉
        routeOrientationSites period edge route
  | [], _, _ => by simp [routeOrientationSites]
  | [_], _, _ => by simp [routeOrientationSites]
  | [_, _], _, _ => by simp [routeOrientationSites]
  | before :: current :: after :: rest, location, vertex => by
      simp only [routeOrientationSites, List.mem_cons]
      intro member
      rcases member with equal | tailMember
      · cases equal
      · exact not_mem_vertex_routeOrientationSites period edge
          (current :: after :: rest) location vertex tailMember

/-- Complete provenance membership for a vertex site confirms that the
stored vertex belongs to the contracted graph. -/
theorem PlanarPresentation.finalOrientationSite_vertex_data
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {location : Cell} {vertex : PeriodicThreeDMVertex}
    (member :
      (location, FinalOrientationSite.vertex vertex) ∈
        presentation.finalOrientationSites) :
    vertex ∈ problem.contractedGraph.vertices := by
  unfold PlanarPresentation.finalOrientationSites at member
  simp only [List.mem_append] at member
  rcases member with vertexMember | routeMember
  · simp only [List.mem_map] at vertexMember
    rcases vertexMember with ⟨listedVertex, listedMember, equal⟩
    cases equal
    exact listedMember
  · simp only [List.mem_flatMap] at routeMember
    rcases routeMember with ⟨edge, edgeMember, siteMember⟩
    exact (not_mem_vertex_routeOrientationSites
      presentation.finalNormalizationPeriod edge
      (presentation.finalNormalizationRoute edge) location vertex
      siteMember).elim

/-- Complete provenance membership for a route site recovers its listed
contracted edge and displayed final-route window. -/
theorem PlanarPresentation.finalOrientationSite_route_data
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {location : Cell} {edge : ContractedEdge}
    {before current after : Cell}
    (member :
      (location, FinalOrientationSite.route edge before current after) ∈
        presentation.finalOrientationSites) :
    edge ∈ problem.contractedEdges ∧
      ∃ leading rest,
        presentation.finalNormalizationRoute edge =
          leading ++ before :: current :: after :: rest := by
  unfold PlanarPresentation.finalOrientationSites at member
  simp only [List.mem_append] at member
  rcases member with vertexMember | routeMember
  · simp only [List.mem_map] at vertexMember
    rcases vertexMember with ⟨vertex, vertexListMember, equal⟩
    cases equal
  · simp only [List.mem_flatMap] at routeMember
    rcases routeMember with ⟨owner, ownerMember, siteMember⟩
    rcases exists_route_triple_of_mem_routeOrientationSites
        presentation.finalNormalizationPeriod owner siteMember with
      ⟨edgeEq, leading, rest, routeEq⟩
    subst owner
    exact ⟨ownerMember, leading, rest, routeEq⟩

/-- Inward values used at one internal route site. -/
def routeSiteInward
    (values : IncidenceTag → Cell → Bool)
    (edge : ContractedEdge) (before current after translate : Cell)
    (side : Side) : Bool :=
  if side = Side.ofAxisDirection
      (AxisDirection.between current before) then
    !(edge.sourceInward values translate)
  else if side = Side.ofAxisDirection
      (AxisDirection.between current after) then
    edge.sourceInward values translate
  else
    false

/-- Two distinct routing sides equipped with complementary values satisfy
the corresponding wire or bend constraint. -/
theorem routingCellType_satisfiesOrientation
    (first second : Side) (different : first ≠ second)
    (color : WireColor) (value : Bool) :
    PeriodicOrthogonalDrawing.satisfiesOrientation
      (routingCellType first second color)
      (fun side =>
        if side = first then !value
        else if side = second then value
        else false) := by
  cases first <;> cases second <;> cases value <;>
    simp_all [routingCellType,
      PeriodicOrthogonalDrawing.satisfiesOrientation]

/-- Every valid displayed route triple satisfies its local wire or bend
constraint under `routeSiteInward`. -/
theorem routingCellTypeAt_satisfiesOrientation
    (values : IncidenceTag → Cell → Bool)
    (edge : ContractedEdge) {before current after : Cell}
    (incoming : AxisDirection.IsUnitAxisStep before current)
    (outgoing : AxisDirection.IsUnitAxisStep current after)
    (noReverse :
      AxisDirection.between current after ≠
        (AxisDirection.between before current).opposite)
    (translate : Cell) :
    PeriodicOrthogonalDrawing.satisfiesOrientation
      (routingCellTypeAt before current after edge.color)
      (routeSiteInward values edge before current after translate) := by
  have incomingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep incoming
  have outgoingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep outgoing
  have backward :
      AxisDirection.between current before =
        (AxisDirection.between before current).opposite :=
    AxisDirection.between_reverse_eq_opposite incomingGenuine
  have backwardGenuine :
      (AxisDirection.between current before).IsGenuine := by
    rw [backward]
    exact AxisDirection.opposite_isGenuine incomingGenuine
  have directionsDifferent :
      AxisDirection.between current before ≠
        AxisDirection.between current after := by
    rw [backward]
    exact Ne.symm noReverse
  have sidesDifferent :
      Side.ofAxisDirection (AxisDirection.between current before) ≠
        Side.ofAxisDirection (AxisDirection.between current after) :=
    Side.ofAxisDirection_injective_of_genuine
      backwardGenuine outgoingGenuine directionsDifferent
  unfold routingCellTypeAt routeSiteInward
  exact routingCellType_satisfiesOrientation
    (Side.ofAxisDirection (AxisDirection.between current before))
    (Side.ofAxisDirection (AxisDirection.between current after))
    sidesDifferent edge.color (edge.sourceInward values translate)

/-- Inward values attached to one finite provenance site at one lifted
geometric translate. -/
def FinalOrientationSite.inward
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (values : problem.GraphOrientation)
    (translate : Cell) : FinalOrientationSite → Side → Bool
  | .vertex v =>
      presentation.vertexPortInward values v translate
  | .route edge before current after =>
      routeSiteInward values edge before current after translate

/-- Every listed provenance site satisfies its local compiled cell
constraint at every lattice translate. -/
theorem ContinuousPlanarPresentation.finalOrientationSite_satisfiesOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    {storedLocation : Cell} {site : FinalOrientationSite}
    (member :
      (storedLocation, site) ∈
        presentation.toPlanarPresentation.finalOrientationSites)
    (translate : Cell) :
    PeriodicOrthogonalDrawing.satisfiesOrientation
      (site.cellType presentation.toPlanarPresentation)
      (site.inward presentation.toPlanarPresentation values translate) := by
  let planar := presentation.toPlanarPresentation
  cases site with
  | vertex vertex =>
      have vertexMember := planar.finalOrientationSite_vertex_data member
      simpa [FinalOrientationSite.cellType, FinalOrientationSite.inward] using
        PlanarPresentation.finalVertexCellType_satisfiesOrientation
          presentation wellFormed degree values valid vertexMember translate
  | route edge before current after =>
      rcases planar.finalOrientationSite_route_data member with
        ⟨edgeMember, leading, rest, routeEq⟩
      have unitSteps := presentation.finalNormalizationRoute_unitSteps
        wellFormed degree edgeMember
      have noReversal :=
        presentation.finalNormalizationRoute_hasNoImmediateReversal
          wellFormed degree edgeMember
      rw [routeEq] at unitSteps noReversal
      have suffixUnitSteps :
          (before :: current :: after :: rest).IsChain
            AxisDirection.IsUnitAxisStep :=
        (List.isChain_append.mp unitSteps).2.1
      have incoming := (List.isChain_cons_cons.mp suffixUnitSteps).1
      have outgoing :=
        (List.isChain_cons_cons.mp
          (List.isChain_cons_cons.mp suffixUnitSteps).2).1
      have suffixNoReversal :
          AxisDirection.HasNoImmediateReversal
            (before :: current :: after :: rest) := by
        simpa using hasNoImmediateReversal_drop noReversal leading.length
      simpa [FinalOrientationSite.cellType, FinalOrientationSite.inward] using
        routingCellTypeAt_satisfiesOrientation values edge incoming outgoing
          suffixNoReversal.1 translate

/-- Plane-wide drawing orientation induced by a suppressed 3DM orientation.
Blank cells and unused sides receive an irrelevant `false` value. -/
noncomputable def ContinuousPlanarPresentation.forwardDrawingOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (values : problem.GraphOrientation) :
    presentation.toPlanarPresentation.normalizedOrthogonalDrawing.Orientation :=
  fun location side =>
    let planar := presentation.toPlanarPresentation
    match planar.finalOrientationSiteAt location with
    | none => false
    | some site =>
        site.inward planar values
          (planar.finalOrientationSiteOccurrenceTranslate location site) side

/-- The forward plane-wide orientation satisfies every local drawing-cell
constraint. -/
theorem ContinuousPlanarPresentation.forwardDrawingOrientation_local
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    (location : Cell) :
    PeriodicOrthogonalDrawing.satisfiesOrientation
      (presentation.toPlanarPresentation.normalizedOrthogonalDrawing.getAt
        location)
      (presentation.forwardDrawingOrientation values location) := by
  let planar := presentation.toPlanarPresentation
  generalize lookup : planar.finalOrientationSiteAt location = found
  cases found with
  | none =>
      have blank :=
        planar.normalizedOrthogonalDrawing_getAt_eq_blank_of_site_none lookup
      rw [blank]
      simp [PeriodicOrthogonalDrawing.satisfiesOrientation]
  | some site =>
      have cellType :=
        planar.normalizedOrthogonalDrawing_getAt_eq_of_site_lookup
          collisionFree lookup
      rw [cellType]
      have orientationEq :
          presentation.forwardDrawingOrientation values location =
            site.inward planar values
              (planar.finalOrientationSiteOccurrenceTranslate location site) := by
        funext side
        unfold ContinuousPlanarPresentation.forwardDrawingOrientation
        dsimp only
        rw [lookup]
      rw [orientationEq]
      exact presentation.finalOrientationSite_satisfiesOrientation
        wellFormed degree values valid (List.mem_of_lookup_eq_some lookup)
          (planar.finalOrientationSiteOccurrenceTranslate location site)

end PeriodicThreeDM

end LeanTrominoes
