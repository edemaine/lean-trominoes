import LeanTrominoes.PeriodicOrthocrossingBendNormalizationDegree
import LeanTrominoes.PeriodicCNFPlanarOccurrences

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- On a nonempty list, `getLastD` is independent of its default. -/
theorem getLastD_eq_of_ne_nil
    {Value : Type*} (values : List Value)
    (nonempty : values ≠ []) (firstDefault secondDefault : Value) :
    values.getLastD firstDefault =
      values.getLastD secondDefault := by
  cases values with
  | nil =>
      exact (nonempty rfl).elim
  | cons first rest =>
      rw [List.getLastD_cons, List.getLastD_cons]

/-- The defaulted last element of a nonempty list is a member. -/
theorem getLastD_mem_of_ne_nil
    {Value : Type*} (values : List Value)
    (nonempty : values ≠ []) (default : Value) :
    values.getLastD default ∈ values := by
  cases values with
  | nil =>
      exact (nonempty rfl).elim
  | cons first rest =>
      rw [getLastD_eq_of_ne_nil
        (first :: rest) (by simp) default first]
      rw [List.getLastD_cons]
      exact List.getLastD_mem_cons

/-- The final tag of a nonempty indexed list is no smaller than its starting
index. -/
theorem zipIdx_getLastD_snd_ge_start
    {Value : Type*} :
    ∀ (values : List Value) (startIndex : Nat)
      (default : Value × Nat),
      values ≠ [] →
        startIndex ≤
          ((values.zipIdx startIndex).getLastD default).2 := by
  intro values
  induction values with
  | nil =>
      intro startIndex default nonempty
      exact (nonempty rfl).elim
  | cons first rest induction =>
      intro startIndex default _nonempty
      cases rest with
      | nil =>
          simp
      | cons second tail =>
          have tailBound :=
            induction (startIndex + 1) (first, startIndex) (by simp)
          change startIndex ≤
            (((second, startIndex + 1) ::
              tail.zipIdx (startIndex + 2)).getLastD
                (first, startIndex)).2
          have tailBound' :
              startIndex + 1 ≤
                (((second, startIndex + 1) ::
                  tail.zipIdx (startIndex + 2)).getLastD
                    (first, startIndex)).2 := by
            simpa using tailBound
          omega

/-- A bend's incoming segment precedes the last segment of its route. -/
theorem routeBendsAux_member_index_lt_lastSegment
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat)
      {routeBend : RouteBend},
      routeBend ∈
          routeBendsAux routeIndex translate startIndex points →
        routeBend.incomingSegmentIndex <
          (((gridPolylineSegments points).zipIdx startIndex).getLastD
            defaultTaggedGridSegment).2 := by
  intro points
  induction points with
  | nil =>
      intro startIndex routeBend routeBendMem
      simp [routeBendsAux] at routeBendMem
  | cons first rest induction =>
      cases rest with
      | nil =>
          intro startIndex routeBend routeBendMem
          simp [routeBendsAux] at routeBendMem
      | cons second rest =>
          cases rest with
          | nil =>
              intro startIndex routeBend routeBendMem
              simp [routeBendsAux] at routeBendMem
          | cons third rest =>
              intro startIndex routeBend routeBendMem
              simp only [routeBendsAux, List.mem_cons] at routeBendMem
              rcases routeBendMem with routeBendEq | routeBendMem
              · subst routeBend
                have tailNonempty :
                    gridPolylineSegments
                      (second :: third :: rest) ≠ [] := by
                  simp [gridPolylineSegments]
                have lastGe :=
                  zipIdx_getLastD_snd_ge_start
                    (gridPolylineSegments
                      (second :: third :: rest))
                    (startIndex + 1)
                    defaultTaggedGridSegment tailNonempty
                have lastEq :
                    ((gridPolylineSegments
                      (first :: second :: third :: rest)).zipIdx
                        startIndex).getLastD
                          defaultTaggedGridSegment =
                      ((gridPolylineSegments
                        (second :: third :: rest)).zipIdx
                          (startIndex + 1)).getLastD
                            defaultTaggedGridSegment := by
                  simp [gridPolylineSegments]
                rw [lastEq]
                change startIndex <
                  (((gridPolylineSegments
                    (second :: third :: rest)).zipIdx
                      (startIndex + 1)).getLastD
                        defaultTaggedGridSegment).2
                omega
              · have tailBound :=
                  induction (startIndex + 1) routeBendMem
                simpa [gridPolylineSegments,
                  defaultTaggedGridSegment] using tailBound

/-- The canonical source terminal uses segment index zero. -/
@[simp]
theorem CNFRouteOccurrence.sourceTerminal_segmentIndex
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    (occurrence.sourceTerminal formula).indexed.segmentIndex = 0 := by
  let graph := PeriodicCNF.incidenceGraph formula
  let points :=
    constructedEdgeRoute graph occurrence.edge occurrence.edgeIndex
  have routeLong : 2 ≤ points.length := by
    unfold points constructedEdgeRoute joinPolylines
    simp only [List.length_append]
    have sourceLong :=
      fanout_length_ge_two
        (vertexX (graph.vertices.idxOf occurrence.edge.source))
        (portX graph
          (sourcePort occurrence.edge occurrence.edgeIndex))
    omega
  have segmentsNonempty :
      gridPolylineSegments points ≠ [] := by
    intro segmentsEmpty
    have lengthZero := congrArg List.length segmentsEmpty
    rw [gridPolylineSegments_length] at lengthZero
    simp only [List.length_nil] at lengthZero
    omega
  unfold CNFRouteOccurrence.sourceTerminal
    CNFRouteOccurrence.taggedSegments
  change
    (((gridPolylineSegments points).zipIdx).getD
      0 defaultTaggedGridSegment).2 = 0
  cases segmentsEq : gridPolylineSegments points with
  | nil =>
      exact (segmentsNonempty segmentsEq).elim
  | cons first rest =>
      simp

/-- The source terminal's indexed segment belongs to the constructed
drawing. -/
theorem CNFRouteOccurrence.sourceTerminal_indexed_mem
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    (occurrence.sourceTerminal formula).indexed ∈
      (drawing
        (PeriodicCNF.incidenceGraph formula)).indexedSegments := by
  let graph := PeriodicCNF.incidenceGraph formula
  let points :=
    constructedEdgeRoute graph occurrence.edge occurrence.edgeIndex
  let segments := (gridPolylineSegments points).zipIdx
  have taggedEdgeMem :=
    occurrence.taggedEdge_mem formula occurrenceMem
  have routeLong : 2 ≤ points.length := by
    unfold points constructedEdgeRoute joinPolylines
    simp only [List.length_append]
    have sourceLong :=
      fanout_length_ge_two
        (vertexX (graph.vertices.idxOf occurrence.edge.source))
        (portX graph
          (sourcePort occurrence.edge occurrence.edgeIndex))
    omega
  have segmentsNonempty : segments ≠ [] := by
    intro segmentsEmpty
    have lengthZero := congrArg List.length segmentsEmpty
    simp only [segments, List.length_zipIdx,
      gridPolylineSegments_length, List.length_nil] at lengthZero
    omega
  unfold CNFRouteOccurrence.sourceTerminal
    CNFRouteOccurrence.taggedSegments
  change
    (⟨occurrence.edgeIndex,
      (segments.getD 0 defaultTaggedGridSegment).2,
      (segments.getD 0 defaultTaggedGridSegment).1⟩ :
      IndexedGridSegment) ∈ (drawing graph).indexedSegments
  cases segmentsEq : segments with
  | nil =>
      exact (segmentsNonempty segmentsEq).elim
  | cons first rest =>
      change
        (⟨occurrence.edgeIndex, first.2, first.1⟩ :
          IndexedGridSegment) ∈ (drawing graph).indexedSegments
      apply
        constructedRouteSegment_mem_drawing_indexedSegments
          graph
          (taggedEdge := (occurrence.edge, occurrence.edgeIndex))
          taggedEdgeMem
          (taggedSegment := first)
      have firstMem : first ∈ segments := by
        rw [segmentsEq]
        simp
      simpa [segments, points] using firstMem

/-- The target terminal's indexed segment likewise belongs to the
constructed drawing. -/
theorem CNFRouteOccurrence.targetTerminal_indexed_mem
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    (occurrence.targetTerminal formula).indexed ∈
      (drawing
        (PeriodicCNF.incidenceGraph formula)).indexedSegments := by
  let graph := PeriodicCNF.incidenceGraph formula
  let points :=
    constructedEdgeRoute graph occurrence.edge occurrence.edgeIndex
  let segments := (gridPolylineSegments points).zipIdx
  have taggedEdgeMem :=
    occurrence.taggedEdge_mem formula occurrenceMem
  have routeLong : 2 ≤ points.length := by
    unfold points constructedEdgeRoute joinPolylines
    simp only [List.length_append]
    have sourceLong :=
      fanout_length_ge_two
        (vertexX (graph.vertices.idxOf occurrence.edge.source))
        (portX graph
          (sourcePort occurrence.edge occurrence.edgeIndex))
    omega
  have segmentsNonempty : segments ≠ [] := by
    intro segmentsEmpty
    have lengthZero := congrArg List.length segmentsEmpty
    simp only [segments, List.length_zipIdx,
      gridPolylineSegments_length, List.length_nil] at lengthZero
    omega
  unfold CNFRouteOccurrence.targetTerminal
    CNFRouteOccurrence.taggedSegments
  change
    (⟨occurrence.edgeIndex,
      (segments.getLastD defaultTaggedGridSegment).2,
      (segments.getLastD defaultTaggedGridSegment).1⟩ :
      IndexedGridSegment) ∈ (drawing graph).indexedSegments
  apply
    constructedRouteSegment_mem_drawing_indexedSegments
      graph
      (taggedEdge := (occurrence.edge, occurrence.edgeIndex))
      taggedEdgeMem
      (taggedSegment :=
        segments.getLastD defaultTaggedGridSegment)
  exact getLastD_mem_of_ne_nil
    segments segmentsNonempty defaultTaggedGridSegment

/-- Every bend on a routed CNF occurrence precedes that occurrence's target
terminal segment. -/
theorem RouteBend.incomingSegmentIndex_lt_targetTerminal
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula)
    {routeBend : RouteBend}
    (routeBendMem :
      routeBend ∈
        drawingRouteBends
          (PeriodicCNF.incidenceGraph formula))
    (routeEq :
      routeBend.routeIndex = occurrence.edgeIndex) :
    routeBend.incomingSegmentIndex <
      (occurrence.targetTerminal formula).indexed.segmentIndex := by
  let graph := PeriodicCNF.incidenceGraph formula
  rcases List.mem_flatMap.mp routeBendMem with
    ⟨taggedRoute, taggedRouteMem, translatedBendsMem⟩
  rcases List.mem_flatMap.mp translatedBendsMem with
    ⟨translate, _translateMem, routeBendMem⟩
  have taggedEdgeMem :=
    occurrence.taggedEdge_mem formula occurrenceMem
  have constructedRouteMem :=
    constructedEdgeRoute_mem_drawing_edgeRoutes_zipIdx
      graph taggedEdgeMem
  have routeBendData :=
    routeBendsAux_member_data taggedRoute.2 translate
      taggedRoute.1 0 routeBendMem
  have routeIndexEq :
      taggedRoute.2 = occurrence.edgeIndex :=
    routeBendData.1.symm.trans routeEq
  have taggedRouteEq :
      taggedRoute =
        (constructedEdgeRoute graph
          occurrence.edge occurrence.edgeIndex,
          occurrence.edgeIndex) :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      taggedRouteMem constructedRouteMem routeIndexEq
  subst taggedRoute
  have bound :=
    routeBendsAux_member_index_lt_lastSegment
      occurrence.edgeIndex translate
      (constructedEdgeRoute graph
        occurrence.edge occurrence.edgeIndex)
      0 routeBendMem
  simpa [CNFRouteOccurrence.targetTerminal,
    CNFRouteOccurrence.taggedSegments, graph] using bound

/-- No normalized bend link is incident to the source terminal of a routed
CNF occurrence. -/
theorem normalizedRouteBendLink_not_incident_sourceTerminal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable)
    {link : PeriodicEquality.NormalizedLink PeriodicCarrierNode}
    (linkMem :
      link ∈
        (drawingRouteBendLinks
          (PeriodicCNF.incidenceGraph formula)).map
            (PeriodicEquality.normalizeLink
              (normalizeCarrierNode
                (PeriodicCNF.incidenceGraph formula)))) :
    ¬(link.first =
          .terminal (occurrence.sourceTerminal formula).indexed .start ∨
      link.second =
          .terminal (occurrence.sourceTerminal formula).indexed .start) := by
  rcases List.mem_map.mp linkMem with
    ⟨source, sourceMem, linkEq⟩
  rcases List.mem_map.mp sourceMem with
    ⟨routeBend, _routeBendMem, sourceEq⟩
  subst link
  subst source
  intro incident
  rcases incident with firstEq | secondEq
  · simp at firstEq
  · have indexedEq :
        routeBend.outgoingTerminal.indexed =
          (occurrence.sourceTerminal formula).indexed :=
      (PeriodicCarrierNode.terminal.inj secondEq).1
    have segmentIndexEq :=
      congrArg IndexedGridSegment.segmentIndex indexedEq
    simp [RouteBend.outgoingTerminal] at segmentIndexEq

/-- No normalized bend link is incident to the target terminal of a listed
routed CNF occurrence. -/
theorem normalizedRouteBendLink_not_incident_targetTerminal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula)
    {link : PeriodicEquality.NormalizedLink PeriodicCarrierNode}
    (linkMem :
      link ∈
        (drawingRouteBendLinks
          (PeriodicCNF.incidenceGraph formula)).map
            (PeriodicEquality.normalizeLink
              (normalizeCarrierNode
                (PeriodicCNF.incidenceGraph formula)))) :
    ¬(link.first =
          .terminal (occurrence.targetTerminal formula).indexed .finish ∨
      link.second =
          .terminal (occurrence.targetTerminal formula).indexed .finish) := by
  rcases List.mem_map.mp linkMem with
    ⟨source, sourceMem, linkEq⟩
  rcases List.mem_map.mp sourceMem with
    ⟨routeBend, routeBendDedupMem, sourceEq⟩
  subst link
  subst source
  have routeBendMem :
      routeBend ∈ drawingRouteBends
        (PeriodicCNF.incidenceGraph formula) :=
    List.mem_dedup.mp routeBendDedupMem
  intro incident
  rcases incident with firstEq | secondEq
  · have indexedEq :
        routeBend.incomingTerminal.indexed =
          (occurrence.targetTerminal formula).indexed :=
      (PeriodicCarrierNode.terminal.inj firstEq).1
    have routeEq :
        routeBend.routeIndex = occurrence.edgeIndex :=
      congrArg IndexedGridSegment.routeIndex indexedEq
    have segmentIndexEq :
        routeBend.incomingSegmentIndex =
          (occurrence.targetTerminal formula).indexed.segmentIndex :=
      congrArg IndexedGridSegment.segmentIndex indexedEq
    have beforeTarget :=
      routeBend.incomingSegmentIndex_lt_targetTerminal
        occurrenceMem routeBendMem routeEq
    omega
  · simp at secondEq

/-- The normalized bend family contributes no endpoint at a routed source
terminal prototype. -/
theorem deduplicatedNormalizedRouteBendLinks_sourceTerminal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRouteBendLinks
        (PeriodicCNF.incidenceGraph formula))).count
          (.terminal
            (occurrence.sourceTerminal formula).indexed .start) = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro targetMem
  rcases List.mem_flatMap.mp targetMem with
    ⟨link, linkMem, endpointMem⟩
  have linkRaw :
      link ∈
        (drawingRouteBendLinks
          (PeriodicCNF.incidenceGraph formula)).map
            (PeriodicEquality.normalizeLink
              (normalizeCarrierNode
                (PeriodicCNF.incidenceGraph formula))) :=
    List.mem_dedup.mp linkMem
  apply normalizedRouteBendLink_not_incident_sourceTerminal
    formula occurrence linkRaw
  simpa [PeriodicEquality.normalizedLinkEndpoints,
    eq_comm] using endpointMem

/-- The normalized bend family likewise contributes no endpoint at a listed
routed target terminal prototype. -/
theorem deduplicatedNormalizedRouteBendLinks_targetTerminal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRouteBendLinks
        (PeriodicCNF.incidenceGraph formula))).count
          (.terminal
            (occurrence.targetTerminal formula).indexed .finish) = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro targetMem
  rcases List.mem_flatMap.mp targetMem with
    ⟨link, linkMem, endpointMem⟩
  have linkRaw :
      link ∈
        (drawingRouteBendLinks
          (PeriodicCNF.incidenceGraph formula)).map
            (PeriodicEquality.normalizeLink
              (normalizeCarrierNode
                (PeriodicCNF.incidenceGraph formula))) :=
    List.mem_dedup.mp linkMem
  apply normalizedRouteBendLink_not_incident_targetTerminal
    formula occurrenceMem linkRaw
  simpa [PeriodicEquality.normalizedLinkEndpoints,
    eq_comm] using endpointMem

/-- Periodically deduplicated bend clauses use no routed source terminal. -/
theorem deduplicatedNormalizedRouteBendFormula_sourceTerminal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    (deduplicatedNormalizedRouteBendFormula
      (PeriodicCNF.incidenceGraph formula)).variableOccurrences.count
        (.terminal
          (occurrence.sourceTerminal formula).indexed .start) = 0 := by
  unfold deduplicatedNormalizedRouteBendFormula
  rw [PeriodicEquality.deduplicatedNormalizedFormula_occurrence_count]
  change 2 *
    (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRouteBendLinks
        (PeriodicCNF.incidenceGraph formula))).count
          (.terminal
            (occurrence.sourceTerminal formula).indexed .start) = 0
  rw [
    deduplicatedNormalizedRouteBendLinks_sourceTerminal_count_eq_zero]

/-- Periodically deduplicated bend clauses use no listed routed target
terminal. -/
theorem deduplicatedNormalizedRouteBendFormula_targetTerminal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    (deduplicatedNormalizedRouteBendFormula
      (PeriodicCNF.incidenceGraph formula)).variableOccurrences.count
        (.terminal
          (occurrence.targetTerminal formula).indexed .finish) = 0 := by
  unfold deduplicatedNormalizedRouteBendFormula
  rw [PeriodicEquality.deduplicatedNormalizedFormula_occurrence_count]
  change 2 *
    (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRouteBendLinks
        (PeriodicCNF.incidenceGraph formula))).count
          (.terminal
            (occurrence.targetTerminal formula).indexed .finish) = 0
  rw [
    deduplicatedNormalizedRouteBendLinks_targetTerminal_count_eq_zero
      formula occurrenceMem]

/-- At a routed source endpoint, the normalized route wire has only its
complete-carrier contribution and therefore at most thirty-six
occurrences. -/
theorem normalizedRouteWireFormula_sourceTerminal_count_le_six
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    (normalizedRouteWireFormula
      (PeriodicCNF.incidenceGraph formula)).variableOccurrences.count
        (.terminal
          (occurrence.sourceTerminal formula).indexed .start) ≤ 6 := by
  have carrierLe :=
    deduplicatedNormalizedCompleteCarrierFormula_terminal_count_le_six
      wellFormed degree isLocal
      (occurrence.sourceTerminal_indexed_mem occurrenceMem) .start
  have bendZero :=
    deduplicatedNormalizedRouteBendFormula_sourceTerminal_count_eq_zero
      formula occurrence
  unfold normalizedRouteWireFormula PeriodicCNF.variableOccurrences
  rw [List.flatMap_append, List.count_append]
  unfold PeriodicCNF.variableOccurrences at carrierLe bendZero
  omega

/-- The same thirty-six-occurrence route-wire bound holds at a routed target
endpoint. -/
theorem normalizedRouteWireFormula_targetTerminal_count_le_six
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    (normalizedRouteWireFormula
      (PeriodicCNF.incidenceGraph formula)).variableOccurrences.count
        (.terminal
          (occurrence.targetTerminal formula).indexed .finish) ≤ 6 := by
  have carrierLe :=
    deduplicatedNormalizedCompleteCarrierFormula_terminal_count_le_six
      wellFormed degree isLocal
      (occurrence.targetTerminal_indexed_mem occurrenceMem) .finish
  have bendZero :=
    deduplicatedNormalizedRouteBendFormula_targetTerminal_count_eq_zero
      formula occurrenceMem
  unfold normalizedRouteWireFormula PeriodicCNF.variableOccurrences
  rw [List.flatMap_append, List.count_append]
  unfold PeriodicCNF.variableOccurrences at carrierLe bendZero
  omega

end PeriodicOrthocrossing
end LeanTrominoes
