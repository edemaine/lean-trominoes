import LeanTrominoes.PeriodicThreeDMVertexNormalizationOccurrenceSeparation

/-!
# First-round normalization drawing separation

The occurrence-level separation theorem is transferred to the finite list
of routes stored in the first intermediate normalization drawing.  The only
additional bookkeeping is recovering the contracted edge at a stored route
index and showing that distinct indexed lifted routes give distinct
contracted-edge occurrences.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

/-- A stored first-round route and its list index recover the contracted edge
at the same index. -/
theorem PlanarPresentation.normalizationGridDrawing1_route_has_edge
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {taggedRoute : List Cell × Nat}
    (member : taggedRoute ∈
      presentation.normalizationGridDrawing1.edgeRoutes.zipIdx) :
    ∃ edge : ContractedEdge,
      (edge, taggedRoute.2) ∈ problem.contractedEdges.zipIdx ∧
        taggedRoute.1 = presentation.normalizationRoute1 edge := by
  have routeIndexLt := (List.mem_zipIdx' member).1
  have edgeIndexLt : taggedRoute.2 < problem.contractedEdges.length := by
    simpa [PlanarPresentation.normalizationGridDrawing1,
      PlanarPresentation.normalizationEdgeRoutes1] using routeIndexLt
  let edge := problem.contractedEdges[taggedRoute.2]'edgeIndexLt
  have edgeMember :
      (edge, taggedRoute.2) ∈ problem.contractedEdges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨edgeIndexLt, rfl⟩
  refine ⟨edge, edgeMember, ?_⟩
  have routeAt :
      presentation.normalizationGridDrawing1.edgeRoute taggedRoute.2 =
        taggedRoute.1 := by
    unfold PeriodicGridDrawing.edgeRoute
    rw [List.getD_eq_getElem _ _ routeIndexLt]
    exact (List.mem_zipIdx' member).2.symm
  exact routeAt.symm.trans
    (presentation.normalizationGridDrawing1_edgeRoute edgeMember)

/-- Complete lifted route separation holds for the stored drawing after the
first vertex-normalization round. -/
theorem ContinuousPlanarPresentation.normalizationGridDrawing1_liftedRoutesAvoidEachOther
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.toPlanarPresentation.normalizationGridDrawing1.LiftedRoutesAvoidEachOther := by
  let planar := presentation.toPlanarPresentation
  intro first firstMember second secondMember
    firstTranslate secondTranslate indicesDifferent
  rcases planar.normalizationGridDrawing1_route_has_edge firstMember with
    ⟨firstEdge, firstEdgeMember, firstRouteEq⟩
  rcases planar.normalizationGridDrawing1_route_has_edge secondMember with
    ⟨secondEdge, secondEdgeMember, secondRouteEq⟩
  have edgeOccurrencesDifferent :
      (firstEdge, firstTranslate) ≠
        (secondEdge, secondTranslate) := by
    intro equal
    apply indicesDifferent
    have edgesEqual : firstEdge = secondEdge :=
      congrArg Prod.fst equal
    have taggedEdgesEqual :=
      tagged_eq_of_mem_zipIdx_of_fst_eq_of_nodup
        (contractedEdges_nodup problem degree)
        firstEdgeMember secondEdgeMember edgesEqual
    have edgeIndicesEqual : first.2 = second.2 :=
      congrArg (fun tagged : ContractedEdge × Nat => tagged.2)
        taggedEdgesEqual
    have translatesEqual : firstTranslate = secondTranslate :=
      congrArg (fun occurrence : ContractedEdge × Cell => occurrence.2)
        equal
    exact Prod.ext edgeIndicesEqual translatesEqual
  have avoids :=
    presentation.normalizationRouteOccurrences1_avoidEachOther
      wellFormed degree separated sourceSimple
      (List.fst_mem_of_mem_zipIdx firstEdgeMember)
      (List.fst_mem_of_mem_zipIdx secondEdgeMember)
      firstTranslate secondTranslate edgeOccurrencesDifferent
  change RoutesAvoidEachOther
    (translatePolyline
      (planar.normalizationGridDrawing1.periodTranslation firstTranslate)
      first.1)
    (translatePolyline
      (planar.normalizationGridDrawing1.periodTranslation secondTranslate)
      second.1)
  rw [firstRouteEq, secondRouteEq]
  exact avoids

end PeriodicThreeDM
end LeanTrominoes
