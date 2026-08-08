import LeanTrominoes.PeriodicGridDrawingLiftedRouteSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreLocalGates

/-!
# Reassembling continuous planarity from lifted interior-contact separation

Some gadget assemblies intentionally allow two distinct routes to list the
same harmless bend point.  They therefore cannot satisfy the stronger
`RoutesAvoidEachOther` predicate, which requires every listed coincidence to
be an outer endpoint.  Continuous planarity needs only the three interior
contact fields: disjoint segment interiors and both directed point/interior
conditions.

This module lifts that weaker finite predicate to periodic route occurrences.
Together with simplicity of each stored route, it implies both global route
predicates.  Standard endpoint coverage then supplies vertex/interior
avoidance without a separate geometric case split for every gadget vertex.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicPlanarOneInThreeToThreeDM

/-- Every pair of distinct complete route occurrences in the periodic lift
avoids all three kinds of segment-interior contact. -/
def LiftedRoutesAvoidInteriorContacts
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.edgeRoutes.zipIdx,
    ∀ second ∈ drawing.edgeRoutes.zipIdx,
      ∀ firstTranslate secondTranslate,
        (first.2, firstTranslate) ≠
            (second.2, secondTranslate) →
          RoutesAvoidInteriorContacts
            (first.1.map
              (Cell.add
                (drawing.periodTranslation firstTranslate)))
            (second.1.map
              (Cell.add
                (drawing.periodTranslation secondTranslate)))

/-- Translation-invariant form of
`LiftedRoutesAvoidInteriorContacts`: keep the first stored route fixed and
translate only the second by the relative lattice shift. -/
def RelativeLiftedRoutesAvoidInteriorContacts
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.edgeRoutes.zipIdx,
    ∀ second ∈ drawing.edgeRoutes.zipIdx,
      ∀ relativeTranslate,
        (first.2, (0, 0)) ≠
            (second.2, relativeTranslate) →
          RoutesAvoidInteriorContacts
            first.1
            (second.1.map
              (Cell.add
                (drawing.periodTranslation relativeTranslate)))

/-- Absolute lifted interior-contact separation is equivalent to checking
one relative translation for each pair of stored routes. -/
theorem liftedRoutesAvoidInteriorContacts_iff_relative
    (drawing : PeriodicGridDrawing) :
    drawing.LiftedRoutesAvoidInteriorContacts ↔
      drawing.RelativeLiftedRoutesAvoidInteriorContacts := by
  constructor
  · intro separated first firstMember second secondMember
      relativeTranslate occurrencesDifferent
    have avoids :=
      separated first firstMember second secondMember
        (0, 0) relativeTranslate occurrencesDifferent
    have zeroTranslate :
        first.1.map
            (Cell.add (drawing.periodTranslation (0, 0))) =
          first.1 := by
      induction first.1 with
      | nil => rfl
      | cons point points induction =>
          simp only [List.map_cons]
          rw [induction]
          congr 1
          apply Prod.ext <;>
            simp [periodTranslation, Cell.add, Cell.scale]
    rwa [zeroTranslate] at avoids
  · intro separated first firstMember second secondMember
      firstTranslate secondTranslate occurrencesDifferent
    let relativeTranslate :=
      Cell.sub secondTranslate firstTranslate
    have relativeOccurrencesDifferent :
        (first.2, (0, 0)) ≠
          (second.2, relativeTranslate) := by
      intro equal
      apply occurrencesDifferent
      have indicesEqual : first.2 = second.2 :=
        congrArg (fun occurrence : Nat × Cell => occurrence.1) equal
      have relativeZero : (0, 0) = relativeTranslate :=
        congrArg (fun occurrence : Nat × Cell => occurrence.2) equal
      apply Prod.ext indicesEqual
      rcases firstTranslate with ⟨firstX, firstY⟩
      rcases secondTranslate with ⟨secondX, secondY⟩
      simp only [relativeTranslate, Cell.sub, Prod.mk.injEq] at relativeZero
      simp only [Prod.mk.injEq]
      constructor <;> omega
    have relativeAvoids :=
      separated first firstMember second secondMember
        relativeTranslate relativeOccurrencesDifferent
    have translatedAvoids :=
      relativeAvoids.translatePolyline
        (drawing.periodTranslation firstTranslate)
    have firstTranslation :
        PeriodicOrthocrossing.translatePolyline
            (drawing.periodTranslation firstTranslate) first.1 =
          first.1.map
            (Cell.add
              (drawing.periodTranslation firstTranslate)) := by
      rfl
    have secondTranslation :
        (second.1.map
            (Cell.add
              (drawing.periodTranslation relativeTranslate))).map
            (Cell.add
              (drawing.periodTranslation firstTranslate)) =
          second.1.map
            (Cell.add
              (drawing.periodTranslation secondTranslate)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro point pointMember
      rcases point with ⟨pointX, pointY⟩
      apply Prod.ext <;>
        simp [periodTranslation, relativeTranslate,
          Cell.add, Cell.sub, Cell.scale] <;>
        ring
    simpa [firstTranslation, secondTranslation,
      PeriodicOrthocrossing.translatePolyline] using translatedAvoids

private theorem tagged_eq_of_mem_zipIdx_of_snd_eq
    {Item : Type*} {items : List Item}
    {first second : Item × Nat}
    (firstMember : first ∈ items.zipIdx)
    (secondMember : second ∈ items.zipIdx)
    (indicesEqual : first.2 = second.2) :
    first = second := by
  apply Prod.ext
  · have firstAt := (List.mem_zipIdx_iff_getElem?).mp firstMember
    have secondAt := (List.mem_zipIdx_iff_getElem?).mp secondMember
    rw [indicesEqual, secondAt] at firstAt
    exact Option.some.inj firstAt.symm
  · exact indicesEqual

private theorem translatedSegment_mem
    {route : List Cell} {segment : GridSegment}
    (segmentMember : segment ∈ gridPolylineSegments route)
    (offset : Cell) :
    segment.translate offset ∈
      gridPolylineSegments (route.map (Cell.add offset)) := by
  rw [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
  exact List.mem_map.mpr ⟨segment, segmentMember, rfl⟩

private theorem translatedTaggedSegment_mem
    {route : List Cell} {tagged : GridSegment × Nat}
    (taggedMember : tagged ∈ (gridPolylineSegments route).zipIdx)
    (offset : Cell) :
    (tagged.1.translate offset, tagged.2) ∈
      (gridPolylineSegments (route.map (Cell.add offset))).zipIdx := by
  rw [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add,
    List.zipIdx_map]
  exact List.mem_map.mpr ⟨tagged, taggedMember, rfl⟩

/-- Lifted interior-contact separation plus simplicity of each stored route
proves the ordered integer-point route avoidance predicate. -/
theorem routesAvoidInteriors_of_liftedRoutesAvoidInteriorContacts
    {drawing : PeriodicGridDrawing}
    (separated : drawing.LiftedRoutesAvoidInteriorContacts)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    drawing.RoutesAvoidInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate point keysDifferent
    firstContains secondContains
  unfold indexedSegments at firstMember secondMember
  rcases List.mem_flatMap.mp firstMember with
    ⟨firstRoute, firstRouteMember, firstSegmentMember⟩
  rcases List.mem_map.mp firstSegmentMember with
    ⟨firstSegment, firstSegmentMember, firstEqual⟩
  have firstTaggedMember :
      firstSegment ∈ (gridPolylineSegments firstRoute.1).zipIdx :=
    firstSegmentMember
  subst first
  rcases List.mem_flatMap.mp secondMember with
    ⟨secondRoute, secondRouteMember, secondSegmentMember⟩
  rcases List.mem_map.mp secondSegmentMember with
    ⟨secondSegment, secondSegmentMember, secondEqual⟩
  have secondTaggedMember :
      secondSegment ∈ (gridPolylineSegments secondRoute.1).zipIdx :=
    secondSegmentMember
  subst second
  let firstOffset := drawing.periodTranslation firstTranslate
  let secondOffset := drawing.periodTranslation secondTranslate
  have firstTranslatedMember :
      firstSegment.1.translate firstOffset ∈
        gridPolylineSegments
          (firstRoute.1.map (Cell.add firstOffset)) :=
    translatedSegment_mem
      (List.fst_mem_of_mem_zipIdx firstTaggedMember) firstOffset
  have secondTranslatedMember :
      secondSegment.1.translate secondOffset ∈
        gridPolylineSegments
          (secondRoute.1.map (Cell.add secondOffset)) :=
    translatedSegment_mem
      (List.fst_mem_of_mem_zipIdx secondTaggedMember) secondOffset
  by_cases occurrencesDifferent :
      (firstRoute.2, firstTranslate) ≠
        (secondRoute.2, secondTranslate)
  · exact
      (separated firstRoute firstRouteMember
        secondRoute secondRouteMember
        firstTranslate secondTranslate occurrencesDifferent)
        |>.firstInterior_not_secondContains
          (firstSegment.1.translate firstOffset) firstTranslatedMember
          (secondSegment.1.translate secondOffset) secondTranslatedMember
          point firstContains secondContains
  · have occurrenceEqual :
        (firstRoute.2, firstTranslate) =
          (secondRoute.2, secondTranslate) :=
      not_ne_iff.mp occurrencesDifferent
    have routeEqual : firstRoute = secondRoute :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstRouteMember secondRouteMember
        (congrArg Prod.fst occurrenceEqual)
    subst secondRoute
    have translateEqual : firstTranslate = secondTranslate :=
      congrArg Prod.snd occurrenceEqual
    subst secondTranslate
    have segmentIndicesDifferent :
        firstSegment.2 ≠ secondSegment.2 := by
      intro indicesEqual
      have segmentEqual : firstSegment = secondSegment :=
        tagged_eq_of_mem_zipIdx_of_snd_eq
          firstTaggedMember secondTaggedMember indicesEqual
      subst secondSegment
      exact keysDifferent rfl
    have translatedSimple :=
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
        (simple firstRoute.1
          (List.fst_mem_of_mem_zipIdx firstRouteMember)) firstOffset
    rcases
        GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
          secondContains with
      secondInterior | secondEndpoint
    · have firstTranslatedTaggedMember :
          (firstSegment.1.translate firstOffset, firstSegment.2) ∈
            (gridPolylineSegments
              (firstRoute.1.map (Cell.add firstOffset))).zipIdx :=
        translatedTaggedSegment_mem firstTaggedMember firstOffset
      have secondTranslatedTaggedMember :
          (secondSegment.1.translate firstOffset, secondSegment.2) ∈
            (gridPolylineSegments
              (firstRoute.1.map (Cell.add firstOffset))).zipIdx :=
        translatedTaggedSegment_mem secondTaggedMember firstOffset
      exact
        (translatedSimple.2.2
          _ firstTranslatedTaggedMember
          _ secondTranslatedTaggedMember
          segmentIndicesDifferent)
          (GridSegment.interiorsMeet_of_interiorContains
            firstContains secondInterior)
    · have endpoints :=
        gridPolylineSegments_endpoints_mem secondTranslatedMember
      rcases secondEndpoint with atStart | atFinish
      · exact
          (translatedSimple.2.1
            (secondSegment.1.translate firstOffset).start endpoints.1
            (firstSegment.1.translate firstOffset) firstTranslatedMember)
            (atStart ▸ firstContains)
      · exact
          (translatedSimple.2.1
            (secondSegment.1.translate firstOffset).finish endpoints.2
            (firstSegment.1.translate firstOffset) firstTranslatedMember)
            (atFinish ▸ firstContains)

/-- Pairwise avoidance of distinct lifted route occurrences, plus local
route simplicity for the same occurrence, gives continuous disjointness of
all globally indexed route-segment interiors. -/
theorem routesHaveDisjointInteriors_of_liftedRoutesAvoidInteriorContacts
    {drawing : PeriodicGridDrawing}
    (separated : drawing.LiftedRoutesAvoidInteriorContacts)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    drawing.RoutesHaveDisjointInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate keysDifferent
  unfold indexedSegments at firstMember secondMember
  rcases List.mem_flatMap.mp firstMember with
    ⟨firstRoute, firstRouteMember, firstSegmentMember⟩
  rcases List.mem_map.mp firstSegmentMember with
    ⟨firstSegment, firstSegmentMember, firstEqual⟩
  have firstSegmentTaggedMember :
      firstSegment ∈ (gridPolylineSegments firstRoute.1).zipIdx :=
    firstSegmentMember
  subst first
  rcases List.mem_flatMap.mp secondMember with
    ⟨secondRoute, secondRouteMember, secondSegmentMember⟩
  rcases List.mem_map.mp secondSegmentMember with
    ⟨secondSegment, secondSegmentMember, secondEqual⟩
  have secondSegmentTaggedMember :
      secondSegment ∈ (gridPolylineSegments secondRoute.1).zipIdx :=
    secondSegmentMember
  subst second
  by_cases occurrencesDifferent :
      (firstRoute.2, firstTranslate) ≠
        (secondRoute.2, secondTranslate)
  · have avoids :=
      separated firstRoute firstRouteMember
        secondRoute secondRouteMember
        firstTranslate secondTranslate occurrencesDifferent
    have firstSegmentIndexLt :
        firstSegment.2 < (gridPolylineSegments firstRoute.1).length :=
      List.snd_lt_of_mem_zipIdx firstSegmentTaggedMember
    have secondSegmentIndexLt :
        secondSegment.2 < (gridPolylineSegments secondRoute.1).length :=
      List.snd_lt_of_mem_zipIdx secondSegmentTaggedMember
    let firstSegmentIndex :
        Fin (gridPolylineSegments firstRoute.1).length :=
      ⟨firstSegment.2, firstSegmentIndexLt⟩
    let secondSegmentIndex :
        Fin (gridPolylineSegments secondRoute.1).length :=
      ⟨secondSegment.2, secondSegmentIndexLt⟩
    have firstSegmentAt :
        (gridPolylineSegments firstRoute.1).get firstSegmentIndex =
          firstSegment.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          firstSegmentTaggedMember)).2
    have secondSegmentAt :
        (gridPolylineSegments secondRoute.1).get secondSegmentIndex =
          secondSegment.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          secondSegmentTaggedMember)).2
    have liftedAvoids :=
      avoids.1
        ⟨firstSegment.2, by
          simpa [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
            using firstSegmentIndexLt⟩
        ⟨secondSegment.2, by
          simpa [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
            using secondSegmentIndexLt⟩
    have firstSegmentElem :
        (gridPolylineSegments firstRoute.1)[firstSegment.2] =
          firstSegment.1 := by
      simpa [firstSegmentIndex, List.get_eq_getElem] using firstSegmentAt
    have secondSegmentElem :
        (gridPolylineSegments secondRoute.1)[secondSegment.2] =
          secondSegment.1 := by
      simpa [secondSegmentIndex, List.get_eq_getElem] using secondSegmentAt
    simpa [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add,
      firstSegmentElem, secondSegmentElem]
      using liftedAvoids
  · have occurrenceEqual :
        (firstRoute.2, firstTranslate) =
          (secondRoute.2, secondTranslate) :=
      not_ne_iff.mp occurrencesDifferent
    have routeEqual : firstRoute = secondRoute :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstRouteMember secondRouteMember
          (congrArg Prod.fst occurrenceEqual)
    subst secondRoute
    have translateEqual : firstTranslate = secondTranslate :=
      congrArg Prod.snd occurrenceEqual
    subst secondTranslate
    have segmentIndicesDifferent :
        firstSegment.2 ≠ secondSegment.2 := by
      intro indicesEqual
      have segmentEqual : firstSegment = secondSegment :=
        tagged_eq_of_mem_zipIdx_of_snd_eq
          firstSegmentTaggedMember secondSegmentTaggedMember
          indicesEqual
      subst secondSegment
      exact keysDifferent rfl
    intro translatedMeet
    have baseMeet :
        GridSegment.InteriorsMeet firstSegment.1 secondSegment.1 :=
      (GridSegment.interiorsMeet_translate_both_iff
        firstSegment.1 secondSegment.1
        (drawing.periodTranslation firstTranslate)).mp translatedMeet
    exact
      (simple firstRoute.1
        (List.fst_mem_of_mem_zipIdx firstRouteMember)).2.2
          firstSegment firstSegmentTaggedMember
          secondSegment secondSegmentTaggedMember
          segmentIndicesDifferent baseMeet

/-- The lifted interior-contact interface proves continuous planarity once
the ordinary combinatorial endpoint coverage and orthogonality obligations
are supplied. -/
theorem isContinuouslyPlanar_of_liftedRoutesAvoidInteriorContacts
    {drawing : PeriodicGridDrawing}
    (separated : drawing.LiftedRoutesAvoidInteriorContacts)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    (covered : drawing.VertexPositionsCoveredBySegmentEndpoints)
    (orthogonal : drawing.IsOrthogonal) :
    drawing.IsContinuouslyPlanar := by
  have routesAvoid : drawing.RoutesAvoidInteriors :=
    routesAvoidInteriors_of_liftedRoutesAvoidInteriorContacts
      separated simple
  exact
    ⟨⟨routesAvoid,
        verticesAvoidRouteInteriors_of_endpointCoverage
          drawing covered orthogonal routesAvoid⟩,
      routesHaveDisjointInteriors_of_liftedRoutesAvoidInteriorContacts
        separated simple⟩

/-- Relative-shift interior-contact separation is the minimal pairwise
hypothesis needed by the global continuous-planarity bridge. -/
theorem isContinuouslyPlanar_of_relativeLiftedRoutesAvoidInteriorContacts
    {drawing : PeriodicGridDrawing}
    (separated : drawing.RelativeLiftedRoutesAvoidInteriorContacts)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    (covered : drawing.VertexPositionsCoveredBySegmentEndpoints)
    (orthogonal : drawing.IsOrthogonal) :
    drawing.IsContinuouslyPlanar :=
  isContinuouslyPlanar_of_liftedRoutesAvoidInteriorContacts
    ((liftedRoutesAvoidInteriorContacts_iff_relative drawing).mpr separated)
    simple covered orthogonal

end PeriodicGridDrawing
end LeanTrominoes
