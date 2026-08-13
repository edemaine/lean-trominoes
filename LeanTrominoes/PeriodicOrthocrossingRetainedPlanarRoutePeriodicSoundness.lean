/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierPeriodicSoundness
import LeanTrominoes.PeriodicOrthocrossingPlanarRouteSoundness

/-!
# Periodic soundness of retained complete routes

Retained carrier representatives propagate a signal across each straight
segment occurrence.  The bend clauses are unchanged from the original finite
route formula, so their equalities can be extracted directly at any block
translate.  Alternating these two facts propagates a signal between the
terminal endpoints of every neighboring constructed incidence route.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 2000000

/-- Every unchanged route-bend equality follows from a satisfying retained
periodic formula at each finite-block translate. -/
theorem retainedDrawingRouteBendLink_assignment_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (translate : Cell)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ drawingRouteBendLinks
        (PeriodicCNF.incidenceGraph formula)) :
    planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier link.first)) =
      planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier link.second)) := by
  let graph := PeriodicCNF.incidenceGraph formula
  let finiteAssignment :=
    planarSATFiniteAssignmentAt formula assignment translate
  have finiteHolds :
      FormulaHolds finiteAssignment
        (retainedDrawingPlanarSATFormula formula) :=
    (retainedDrawingPeriodicPlanarSATFormula_satisfies_iff
      formula assignment).mp satisfies translate
  have coreHolds :
      FormulaHolds
          (finiteAssignment ∘ planarSATCoreVariableMap)
          (retainedDrawingRoutePlanarCoreFormula graph) :=
    (retainedDrawingPlanarSATFormula_holds_iff
      formula finiteAssignment).mp finiteHolds |>.1
  have wireHolds :
      FormulaHolds
          ((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl)
          (retainedDrawingRouteWireFormula graph) :=
    (retainedDrawingRoutePlanarCoreFormula_holds_iff
      graph (finiteAssignment ∘ planarSATCoreVariableMap)).mp
        coreHolds |>.2
  have bendHolds :
      FormulaHolds
          ((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl)
          (drawingRouteBendFormula graph) :=
    (formulaHolds_route_append_iff
      ((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl)
      (retainedDrawingCompleteCarrierFormula graph)
      (drawingRouteBendFormula graph)).mp
        (by simpa [retainedDrawingRouteWireFormula] using
          wireHolds) |>.2
  have laws :=
    (equalityFamily_holds_iff
      (((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl))
      (drawingRouteBendLinks graph)).mp
        (by simpa [drawingRouteBendFormula] using bendHolds)
  simpa [Function.comp_def, planarSATCoreVariableMap] using
    laws link linkMem

/-- A satisfying retained periodic formula propagates one value from the
first segment terminal to the last segment terminal of every listed
neighboring constructed route. -/
theorem retainedConstructedRouteTerminals_assignment_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (blockTranslate : Cell)
    {taggedEdge :
      PeriodicEdge (CNFVertex Variable) × Nat}
    (taggedEdgeMem :
      taggedEdge ∈
        (PeriodicCNF.incidenceGraph formula).edges.zipIdx)
    (translate : Cell)
    (translateNeighbor : IsNeighborTranslation translate)
    (default : GridSegment × Nat) :
    let graph := PeriodicCNF.incidenceGraph formula
    let segments :=
      (gridPolylineSegments
        (constructedEdgeRoute graph
          taggedEdge.1 taggedEdge.2)).zipIdx
    let first := segments.getD 0 default
    let last := segments.getLastD default
    planarSATFiniteAssignmentAt formula assignment blockTranslate
          (.inl (.carrier (.terminal
            (taggedRouteSegmentTerminal taggedEdge.2 translate
              first .start)))) =
      planarSATFiniteAssignmentAt formula assignment blockTranslate
          (.inl (.carrier (.terminal
            (taggedRouteSegmentTerminal taggedEdge.2 translate
              last .finish)))) := by
  let graph := PeriodicCNF.incidenceGraph formula
  let points :=
    constructedEdgeRoute graph taggedEdge.1 taggedEdge.2
  let segments :=
    (gridPolylineSegments points).zipIdx
  have routeLong : 2 ≤ points.length := by
    unfold points constructedEdgeRoute joinPolylines
    simp only [List.length_append]
    have sourceLong :=
      fanout_length_ge_two
        (vertexX (graph.vertices.idxOf taggedEdge.1.source))
        (portX graph (sourcePort taggedEdge.1 taggedEdge.2))
    omega
  have segmentsNonempty : segments ≠ [] := by
    intro segmentsEmpty
    have lengthZero := congrArg List.length segmentsEmpty
    simp only [segments, List.length_zipIdx,
      gridPolylineSegments_length, List.length_nil] at lengthZero
    omega
  have segmentLaws :
      ∀ taggedSegment ∈ segments,
        planarSATFiniteAssignmentAt formula assignment blockTranslate
              (.inl (.carrier (.terminal
                (taggedRouteSegmentTerminal taggedEdge.2 translate
                  taggedSegment .start)))) =
          planarSATFiniteAssignmentAt formula assignment blockTranslate
              (.inl (.carrier (.terminal
                (taggedRouteSegmentTerminal taggedEdge.2 translate
                  taggedSegment .finish)))) := by
    intro taggedSegment taggedSegmentMem
    exact
      retainedSegmentOccurrenceTerminals_assignment_eq
        formula wellFormed degree isLocal assignment satisfies
        blockTranslate
        ⟨taggedEdge.2, taggedSegment.2, taggedSegment.1⟩
        (constructedRouteSegment_mem_drawing_indexedSegments
          graph taggedEdgeMem taggedSegmentMem)
        translate translateNeighbor
  have bendLawsForRoute :
      ∀ routeBend ∈
          routeBends taggedEdge.2 translate points,
        planarSATFiniteAssignmentAt formula assignment blockTranslate
              (.inl (.carrier
                (.terminal routeBend.incomingTerminal))) =
          planarSATFiniteAssignmentAt formula assignment blockTranslate
              (.inl (.carrier
                (.terminal routeBend.outgoingTerminal))) := by
    intro routeBend routeBendMem
    apply
      retainedDrawingRouteBendLink_assignment_eq
        formula assignment satisfies blockTranslate
        (link := routeBend.equalityLink graph)
    apply List.mem_map.mpr
    refine ⟨routeBend, ?_, rfl⟩
    apply List.mem_dedup.mpr
    apply List.mem_flatMap.mpr
    refine
      ⟨(points, taggedEdge.2),
        constructedEdgeRoute_mem_drawing_edgeRoutes_zipIdx
          graph taggedEdgeMem, ?_⟩
    apply List.mem_flatMap.mpr
    exact
      ⟨translate,
        (mem_neighborTranslations_iff translate).mpr
          translateNeighbor,
        routeBendMem⟩
  cases segmentsEq : segments with
  | nil =>
      exact (segmentsNonempty segmentsEq).elim
  | cons first rest =>
      let carrierAssignment : CarrierNode → Bool :=
        fun node =>
          planarSATFiniteAssignmentAt formula assignment blockTranslate
            (.inl (.carrier node))
      have propagated :=
        routeTerminals_assignment_eq_aux
          carrierAssignment taggedEdge.2 translate
          points 0 first rest
          (by simpa [segments] using segmentsEq)
          (by simpa [segments, carrierAssignment] using segmentLaws)
          (by simpa [routeBends, carrierAssignment] using
            bendLawsForRoute)
      have defaultEq :
          (first :: rest).getLastD default =
            (first :: rest).getLastD first := by
        rw [List.getLastD_cons, List.getLastD_cons]
      rw [← defaultEq] at propagated
      have firstDefaultEq :
          segments.getD 0 default = first := by
        rw [segmentsEq]
        rfl
      have lastDefaultEq :
          segments.getLastD default =
            (first :: rest).getLastD default := by
        rw [segmentsEq]
      change
        planarSATFiniteAssignmentAt formula assignment blockTranslate
              (.inl (.carrier (.terminal
                (taggedRouteSegmentTerminal taggedEdge.2 translate
                  (segments.getD 0 default) .start)))) =
          planarSATFiniteAssignmentAt formula assignment blockTranslate
              (.inl (.carrier (.terminal
                (taggedRouteSegmentTerminal taggedEdge.2 translate
                  (segments.getLastD default) .finish))))
      rw [firstDefaultEq, lastDefaultEq]
      simpa [points, carrierAssignment,
        taggedRouteSegmentTerminal] using propagated

end PeriodicOrthocrossing
end LeanTrominoes
