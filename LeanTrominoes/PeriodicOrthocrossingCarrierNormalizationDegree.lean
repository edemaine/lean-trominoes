import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalDegree
import LeanTrominoes.PeriodicEqualityNormalization

/-!
# Periodic degree of normalized complete-carrier equalities

Explicit neighboring translations make the finite complete-carrier family
look too large after terminal variables are identified periodically.  This
file quotients its equality links by periodic endpoint normalization.

For a fixed terminal prototype, every distinct normalized incident link is
classified either as the single direct terminal-to-terminal link or by the
translation of a crossing boundary.  The direct class is unique because
terminals are strict extremes of their sorted carrier chains; the geometric
translation bound supplies at most two crossing classes.  Thus normalized
link endpoint degree is at most three, and the two-clause equality encoding
uses a terminal prototype at most six times after clause deduplication.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Carrier-node names after explicit segment translations have been moved
to periodic literal offsets. -/
inductive PeriodicCarrierNode
  | terminal (indexed : IndexedGridSegment) (endpoint : SegmentEnd)
  | boundary (boundary : CrossingBoundary)
  deriving DecidableEq, Repr

def SegmentEnd.other : SegmentEnd → SegmentEnd
  | .start => .finish
  | .finish => .start

@[simp]
theorem SegmentEnd.other_start :
    SegmentEnd.start.other = .finish := rfl

@[simp]
theorem SegmentEnd.other_finish :
    SegmentEnd.finish.other = .start := rfl

theorem SegmentEnd.eq_other_of_ne
    {first second : SegmentEnd}
    (different : first ≠ second) :
    first = second.other := by
  cases first <;> cases second <;> simp_all

def terminalDirectNormalizedLink
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    PeriodicEquality.NormalizedLink PeriodicCarrierNode :=
  let target : PeriodicCarrierNode :=
    .terminal indexed endpoint
  let other : PeriodicCarrierNode :=
    .terminal indexed endpoint.other
  if (⟨indexed, (0, 0), endpoint⟩ :
      SegmentTerminal).IsLower then
    ⟨target, other, (0, 0)⟩
  else
    ⟨other, target, (0, 0)⟩

theorem segmentTerminal_isLower_zero_iff
    (indexed : IndexedGridSegment)
    (translate : Cell) (endpoint : SegmentEnd) :
    (⟨indexed, translate, endpoint⟩ :
        SegmentTerminal).IsLower ↔
      (⟨indexed, (0, 0), endpoint⟩ :
        SegmentTerminal).IsLower :=
  Iff.rfl

theorem SegmentTerminal.eq_of_fields_eq
    {first second : SegmentTerminal}
    (indexedEq : first.indexed = second.indexed)
    (translateEq : first.translate = second.translate)
    (endpointEq : first.endpoint = second.endpoint) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Periodic normalization restricted to complete-carrier variables. -/
def normalizeCarrierNode
    (node : CarrierNode) : PeriodicCarrierNode × Cell :=
  match node with
  | .terminal terminal =>
      (.terminal terminal.indexed terminal.endpoint,
        terminal.translate)
  | .boundary boundary =>
      (.boundary boundary, (0, 0))

@[simp]
theorem normalizeCarrierNode_terminal
    (terminal : SegmentTerminal) :
    normalizeCarrierNode (.terminal terminal) =
      (.terminal terminal.indexed terminal.endpoint,
        terminal.translate) := rfl

@[simp]
theorem normalizeCarrierNode_boundary
    (boundary : CrossingBoundary) :
    normalizeCarrierNode (.boundary boundary) =
      (.boundary boundary, (0, 0)) := rfl

theorem normalizeCarrierNode_fst_eq_terminal_iff
    (node : CarrierNode)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    (normalizeCarrierNode node).1 =
        .terminal indexed endpoint ↔
      ∃ translate,
        node = .terminal ⟨indexed, translate, endpoint⟩ := by
  cases node with
  | boundary boundary =>
      simp [normalizeCarrierNode]
  | terminal terminal =>
      rcases terminal with ⟨nodeIndexed, translate, nodeEndpoint⟩
      simp [normalizeCarrierNode]

theorem equalityLink_eq_of_common_endpoint_count_le_one
    {Variable : Type*} [DecidableEq Variable]
    {links : List (EqualityLink Variable)}
    {node : Variable}
    (countLe :
      (equalityLinkEndpoints links).count node ≤ 1)
    {first second : EqualityLink Variable}
    (firstMem : first ∈ links)
    (secondMem : second ∈ links)
    (firstIncident :
      first.first = node ∨ first.second = node)
    (secondIncident :
      second.first = node ∨ second.second = node) :
    first = second := by
  induction links with
  | nil =>
      simp at firstMem
  | cons head tail induction =>
      simp only [List.mem_cons] at firstMem secondMem
      rcases firstMem with firstEq | firstMem <;>
        rcases secondMem with secondEq | secondMem
      · exact firstEq.trans secondEq.symm
      · subst first
        exfalso
        unfold equalityLinkEndpoints at countLe
        simp only [List.flatMap_cons, List.count_append,
          List.count_cons, List.count_nil] at countLe
        have headPositive :
            1 ≤ [head.first, head.second].count node := by
          rcases firstIncident with incident | incident <;>
            simp [incident]
        simp only [List.count_cons, List.count_nil] at headPositive
        have tailMember :
            node ∈ equalityLinkEndpoints tail := by
          apply List.mem_flatMap.mpr
          exact ⟨second, secondMem, by
            rcases secondIncident with incident | incident <;>
              simp [incident]⟩
        have tailPositive :
            1 ≤ (equalityLinkEndpoints tail).count node :=
          List.count_pos_iff.mpr tailMember
        change 1 ≤
          (tail.flatMap fun link =>
            [link.first, link.second]).count node at tailPositive
        omega
      · subst second
        exfalso
        unfold equalityLinkEndpoints at countLe
        simp only [List.flatMap_cons, List.count_append,
          List.count_cons, List.count_nil] at countLe
        have headPositive :
            1 ≤ [head.first, head.second].count node := by
          rcases secondIncident with incident | incident <;>
            simp [incident]
        simp only [List.count_cons, List.count_nil] at headPositive
        have tailMember :
            node ∈ equalityLinkEndpoints tail := by
          apply List.mem_flatMap.mpr
          exact ⟨first, firstMem, by
            rcases firstIncident with incident | incident <;>
              simp [incident]⟩
        have tailPositive :
            1 ≤ (equalityLinkEndpoints tail).count node :=
          List.count_pos_iff.mpr tailMember
        change 1 ≤
          (tail.flatMap fun link =>
            [link.first, link.second]).count node at tailPositive
        omega
      · apply induction
        · unfold equalityLinkEndpoints at countLe ⊢
          simp only [List.flatMap_cons, List.count_append,
            List.count_cons, List.count_nil] at countLe
          omega
        · exact firstMem
        · exact secondMem

theorem completeCarrierLinks_eq_of_terminal_incident
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    {first second : EqualityLink CarrierNode}
    (firstMem :
      first ∈ completeCarrierLinks graph terminal.carrierKey)
    (secondMem :
      second ∈ completeCarrierLinks graph terminal.carrierKey)
    (firstIncident :
      first.first = .terminal terminal ∨
        first.second = .terminal terminal)
    (secondIncident :
      second.first = .terminal terminal ∨
        second.second = .terminal terminal) :
    first = second := by
  apply equalityLink_eq_of_common_endpoint_count_le_one
    (completeCarrierLinks_terminal_endpoint_count_le_one
      wellFormed degree isLocal terminalMem)
    firstMem secondMem firstIncident secondIncident

theorem normalizeLink_first_eq_terminal_iff
    (link : EqualityLink CarrierNode)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    (PeriodicEquality.normalizeLink
        normalizeCarrierNode link).first =
          .terminal indexed endpoint ↔
      ∃ translate,
        link.first =
          .terminal ⟨indexed, translate, endpoint⟩ := by
  exact normalizeCarrierNode_fst_eq_terminal_iff
    link.first indexed endpoint

theorem normalizeLink_second_eq_terminal_iff
    (link : EqualityLink CarrierNode)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    (PeriodicEquality.normalizeLink
        normalizeCarrierNode link).second =
          .terminal indexed endpoint ↔
      ∃ translate,
        link.second =
          .terminal ⟨indexed, translate, endpoint⟩ := by
  exact normalizeCarrierNode_fst_eq_terminal_iff
    link.second indexed endpoint

theorem drawingCompleteCarrierLink_mem_terminal_chain
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    link ∈ completeCarrierLinks graph terminal.carrierKey := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, linkMem⟩
  have common :=
    completeCarrierLinks_common_key graph key linkMem
  have keyEq : key = terminal.carrierKey := by
    rcases incident with incident | incident
    · simpa [incident, CarrierNode.carrierKey] using common.1.symm
    · simpa [incident, CarrierNode.carrierKey] using common.2.symm
  simpa [keyEq] using linkMem

theorem drawingCompleteCarrierLink_endpoints_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    link.first ∈ drawingCarrierNodes graph ∧
      link.second ∈ drawingCarrierNodes graph := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, linkMem⟩
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEq⟩
  subst link
  have rawPairMem :=
    (List.mem_filter.mp pairMem).1
  have members :=
    mem_of_mem_consecutivePairs rawPairMem
  exact
    ⟨(mem_completeCarrierNodes_iff
        graph key pair.1).mp members.1 |>.1,
      (mem_completeCarrierNodes_iff
        graph key pair.2).mp members.2 |>.1⟩

theorem drawingCompleteCarrierLink_terminal_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    terminal ∈ drawingSegmentTerminals graph := by
  have endpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph linkMem
  rcases incident with incident | incident
  · rw [incident] at endpoints
    rcases List.mem_append.mp endpoints.1 with
      terminalMem | boundaryMem
    · simpa using terminalMem
    · simp at boundaryMem
  · rw [incident] at endpoints
    rcases List.mem_append.mp endpoints.2 with
      terminalMem | boundaryMem
    · simpa using terminalMem
    · simp at boundaryMem

theorem completeCarrierLink_terminal_orientation
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ completeCarrierLinks graph terminal.carrierKey)
    (incident :
      link.first = .terminal terminal ∨
        link.second = .terminal terminal) :
    if terminal.IsLower then
      link.first = .terminal terminal
    else
      link.second = .terminal terminal := by
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEq⟩
  subst link
  have rawPairMem :=
    (List.mem_filter.mp pairMem).1
  have members :=
    mem_of_mem_consecutivePairs rawPairMem
  have nodesNodup :=
    completeCarrierNodes_nodup graph terminal.carrierKey
  have pairNe :=
    consecutivePairs_ne_of_nodup nodesNodup rawPairMem
  have nodesSorted :
      (completeCarrierNodes graph terminal.carrierKey).Pairwise
        fun first second =>
          first.orderCoordinate graph ≤
            second.orderCoordinate graph := by
    unfold completeCarrierNodes
    exact List.pairwise_insertionSort _ _
  have ordered :=
    consecutivePairs_rel_of_pairwise nodesSorted rawPairMem
  simp only [carrierNodePairLink] at incident ⊢
  by_cases lower : terminal.IsLower
  · rw [if_pos lower]
    rcases incident with firstEq | secondEq
    · exact firstEq
    · have firstData :=
        (mem_completeCarrierNodes_iff
          graph terminal.carrierKey pair.1).mp members.1
      have firstDifferent :
          pair.1 ≠ .terminal terminal := by
        intro firstEq
        exact pairNe (firstEq.trans secondEq.symm)
      have extreme :=
        carrierNode_terminal_extreme
          wellFormed degree isLocal terminalMem
            firstData.1 firstData.2 firstDifferent
      rw [if_pos lower] at extreme
      rw [secondEq] at ordered
      omega
  · rw [if_neg lower]
    rcases incident with firstEq | secondEq
    · have secondData :=
        (mem_completeCarrierNodes_iff
          graph terminal.carrierKey pair.2).mp members.2
      have secondDifferent :
          pair.2 ≠ .terminal terminal := by
        intro secondEq
        exact pairNe (firstEq.trans secondEq.symm)
      have extreme :=
        carrierNode_terminal_extreme
          wellFormed degree isLocal terminalMem
            secondData.1 secondData.2 secondDifferent
      rw [if_neg lower] at extreme
      rw [firstEq] at ordered
      omega
    · exact secondEq

theorem completeCarrierLink_endpoints_ne
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ completeCarrierLinks graph key) :
    link.first ≠ link.second := by
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEq⟩
  subst link
  simp only [carrierNodePairLink]
  exact consecutivePairs_ne_of_nodup
    (completeCarrierNodes_nodup graph key)
    (List.mem_filter.mp pairMem).1

theorem drawingCompleteCarrierLink_endpoints_ne
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    link.first ≠ link.second := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, linkMem⟩
  exact completeCarrierLink_endpoints_ne graph key linkMem

/-- Direct terminal-to-terminal links use the distinguished class `none`;
links to a crossing boundary use the segment occurrence's translation. -/
def periodicCarrierNodeClass :
    PeriodicCarrierNode → Option Cell
  | .terminal _ _ => none
  | .boundary boundary => some boundary.translate

/-- Classify the endpoint opposite a fixed terminal in a normalized link. -/
def normalizedTerminalLinkClass
    (target : PeriodicCarrierNode)
    (link : PeriodicEquality.NormalizedLink PeriodicCarrierNode) :
    Option Cell :=
  if link.first = target then
    periodicCarrierNodeClass link.second
  else
    periodicCarrierNodeClass link.first

@[simp]
theorem normalizedTerminalLinkClass_of_first
    (target : PeriodicCarrierNode)
    (link : PeriodicEquality.NormalizedLink PeriodicCarrierNode)
    (firstEq : link.first = target) :
    normalizedTerminalLinkClass target link =
      periodicCarrierNodeClass link.second := by
  simp [normalizedTerminalLinkClass, firstEq]

@[simp]
theorem normalizedTerminalLinkClass_of_second
    (target : PeriodicCarrierNode)
    (link : PeriodicEquality.NormalizedLink PeriodicCarrierNode)
    (firstNe : link.first ≠ target)
    (_secondEq : link.second = target) :
    normalizedTerminalLinkClass target link =
      periodicCarrierNodeClass link.first := by
  simp [normalizedTerminalLinkClass, firstNe]

theorem normalizedLink_incident_terminal_iff
    (link : EqualityLink CarrierNode)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    let normalized :=
      PeriodicEquality.normalizeLink normalizeCarrierNode link
    normalized.first = .terminal indexed endpoint ∨
        normalized.second = .terminal indexed endpoint ↔
      ∃ translate,
        link.first =
            .terminal ⟨indexed, translate, endpoint⟩ ∨
          link.second =
            .terminal ⟨indexed, translate, endpoint⟩ := by
  constructor
  · intro incident
    rcases incident with incident | incident
    · rcases (normalizeLink_first_eq_terminal_iff
        link indexed endpoint).mp incident with
        ⟨translate, terminalEq⟩
      exact ⟨translate, Or.inl terminalEq⟩
    · rcases (normalizeLink_second_eq_terminal_iff
        link indexed endpoint).mp incident with
        ⟨translate, terminalEq⟩
      exact ⟨translate, Or.inr terminalEq⟩
  · rintro ⟨translate, incident⟩
    rcases incident with incident | incident
    · exact Or.inl ((normalizeLink_first_eq_terminal_iff
        link indexed endpoint).mpr ⟨translate, incident⟩)
    · exact Or.inr ((normalizeLink_second_eq_terminal_iff
        link indexed endpoint).mpr ⟨translate, incident⟩)

theorem normalizedTerminalLinkClass_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    (incident :
      let normalized :=
        PeriodicEquality.normalizeLink normalizeCarrierNode link
      normalized.first = .terminal indexed endpoint ∨
        normalized.second = .terminal indexed endpoint) :
    normalizedTerminalLinkClass (.terminal indexed endpoint)
        (PeriodicEquality.normalizeLink normalizeCarrierNode link) ∈
      none ::
        (segmentCrossingTranslations graph indexed).toList.map some := by
  rcases (normalizedLink_incident_terminal_iff
    link indexed endpoint).mp incident with
    ⟨translate, sourceIncident⟩
  let terminal : SegmentTerminal :=
    ⟨indexed, translate, endpoint⟩
  have terminalMem :
      terminal ∈ drawingSegmentTerminals graph :=
    drawingCompleteCarrierLink_terminal_mem
      graph linkMem sourceIncident
  have endpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph linkMem
  have common :=
    drawingCompleteCarrierLinks_common_key graph linkMem
  rcases sourceIncident with firstEq | secondEq
  · cases otherEq : link.second with
    | terminal other =>
        simp [normalizedTerminalLinkClass,
          PeriodicEquality.normalizeLink,
          normalizeCarrierNode, periodicCarrierNodeClass,
          firstEq, otherEq]
    | boundary boundary =>
        have boundaryMem :
            boundary ∈ drawingCrossingBoundaries graph := by
          rw [otherEq] at endpoints
          have nodeMem := endpoints.2
          unfold drawingCarrierNodes at nodeMem
          simpa using nodeMem
        have keyEq :
            boundary.carrierKey = terminal.carrierKey := by
          rw [firstEq, otherEq] at common
          simpa [CarrierNode.carrierKey] using common.symm
        have carrierData :=
          crossingBoundary_terminal_indexed_translate_eq_of_carrierKey_eq
            graph boundaryMem terminalMem keyEq
        have crossingTranslateMem :=
          (drawingCrossingBoundary_indexed_mem_and_translate_mem
            graph boundaryMem).2
        rw [carrierData.1] at crossingTranslateMem
        change boundary.translate ∈
          segmentCrossingTranslations graph indexed
            at crossingTranslateMem
        simp [normalizedTerminalLinkClass,
          PeriodicEquality.normalizeLink,
          normalizeCarrierNode, periodicCarrierNodeClass,
          firstEq, otherEq,
          crossingTranslateMem]
  · cases otherEq : link.first with
    | terminal other =>
        simp [normalizedTerminalLinkClass,
          PeriodicEquality.normalizeLink,
          normalizeCarrierNode, periodicCarrierNodeClass,
          secondEq, otherEq]
    | boundary boundary =>
        have boundaryMem :
            boundary ∈ drawingCrossingBoundaries graph := by
          rw [otherEq] at endpoints
          have nodeMem := endpoints.1
          unfold drawingCarrierNodes at nodeMem
          simpa using nodeMem
        have keyEq :
            boundary.carrierKey = terminal.carrierKey := by
          rw [otherEq, secondEq] at common
          simpa [CarrierNode.carrierKey] using common
        have carrierData :=
          crossingBoundary_terminal_indexed_translate_eq_of_carrierKey_eq
            graph boundaryMem terminalMem keyEq
        have crossingTranslateMem :=
          (drawingCrossingBoundary_indexed_mem_and_translate_mem
            graph boundaryMem).2
        rw [carrierData.1] at crossingTranslateMem
        change boundary.translate ∈
          segmentCrossingTranslations graph indexed
            at crossingTranslateMem
        simp [normalizedTerminalLinkClass,
          PeriodicEquality.normalizeLink,
          normalizeCarrierNode, periodicCarrierNodeClass,
          secondEq, otherEq,
          crossingTranslateMem]

theorem normalizedTerminalLinkClass_some_eq_terminal_translate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    (translate classTranslate : Cell)
    (sourceIncident :
      link.first =
          .terminal ⟨indexed, translate, endpoint⟩ ∨
        link.second =
          .terminal ⟨indexed, translate, endpoint⟩)
    (classEq :
      normalizedTerminalLinkClass (.terminal indexed endpoint)
          (PeriodicEquality.normalizeLink
            normalizeCarrierNode link) =
        some classTranslate) :
    translate = classTranslate := by
  let terminal : SegmentTerminal :=
    ⟨indexed, translate, endpoint⟩
  have common :=
    drawingCompleteCarrierLinks_common_key graph linkMem
  rcases sourceIncident with firstEq | secondEq
  · cases otherEq : link.second with
    | terminal other =>
        simp [normalizedTerminalLinkClass,
          PeriodicEquality.normalizeLink,
          normalizeCarrierNode, periodicCarrierNodeClass,
          firstEq, otherEq] at classEq
    | boundary boundary =>
        have keyEq :
            terminal.carrierKey = boundary.carrierKey := by
          rw [firstEq, otherEq] at common
          simpa [CarrierNode.carrierKey] using common
        have translateEq :
            translate = boundary.translate := by
          simpa [SegmentTerminal.carrierKey,
            PeriodicGridDrawing.SegmentOccurrenceKey] using
            congrArg (fun key => key.2.2)
              (keyEq.trans
                (CrossingBoundary.carrierKey_eq_indexed_translate
                  boundary))
        simp [normalizedTerminalLinkClass,
          PeriodicEquality.normalizeLink,
          normalizeCarrierNode, periodicCarrierNodeClass,
          firstEq, otherEq] at classEq
        exact translateEq.trans classEq
  · cases otherEq : link.first with
    | terminal other =>
        simp [normalizedTerminalLinkClass,
          PeriodicEquality.normalizeLink,
          normalizeCarrierNode, periodicCarrierNodeClass,
          secondEq, otherEq] at classEq
    | boundary boundary =>
        have keyEq :
            boundary.carrierKey = terminal.carrierKey := by
          rw [otherEq, secondEq] at common
          simpa [CarrierNode.carrierKey] using common
        have translateEq :
            boundary.translate = translate := by
          simpa [SegmentTerminal.carrierKey,
            PeriodicGridDrawing.SegmentOccurrenceKey] using
            congrArg (fun key => key.2.2)
              ((CrossingBoundary.carrierKey_eq_indexed_translate
                boundary).symm.trans keyEq)
        simp [normalizedTerminalLinkClass,
          PeriodicEquality.normalizeLink,
          normalizeCarrierNode, periodicCarrierNodeClass,
          secondEq, otherEq] at classEq
        exact translateEq.symm.trans classEq

theorem normalizeLink_eq_terminalDirectNormalizedLink_of_class_none
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph)
    (incident :
      let normalized :=
        PeriodicEquality.normalizeLink normalizeCarrierNode link
      normalized.first = .terminal indexed endpoint ∨
        normalized.second = .terminal indexed endpoint)
    (classEq :
      normalizedTerminalLinkClass (.terminal indexed endpoint)
          (PeriodicEquality.normalizeLink
            normalizeCarrierNode link) = none) :
    PeriodicEquality.normalizeLink normalizeCarrierNode link =
      terminalDirectNormalizedLink indexed endpoint := by
  rcases (normalizedLink_incident_terminal_iff
    link indexed endpoint).mp incident with
    ⟨translate, sourceIncident⟩
  let terminal : SegmentTerminal :=
    ⟨indexed, translate, endpoint⟩
  have terminalMem :
      terminal ∈ drawingSegmentTerminals graph :=
    drawingCompleteCarrierLink_terminal_mem
      graph linkMem sourceIncident
  have chainMem :=
    drawingCompleteCarrierLink_mem_terminal_chain
      graph linkMem sourceIncident
  have orientation :=
    completeCarrierLink_terminal_orientation
      wellFormed degree isLocal terminalMem chainMem sourceIncident
  have endpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph linkMem
  have common :=
    drawingCompleteCarrierLinks_common_key graph linkMem
  have endpointsNe :=
    drawingCompleteCarrierLink_endpoints_ne graph linkMem
  rcases sourceIncident with firstEq | secondEq
  · cases otherEq : link.second with
    | boundary boundary =>
        simp [normalizedTerminalLinkClass,
          PeriodicEquality.normalizeLink,
          normalizeCarrierNode, periodicCarrierNodeClass,
          firstEq, otherEq] at classEq
    | terminal other =>
        have otherMem :
            other ∈ drawingSegmentTerminals graph := by
          rw [otherEq] at endpoints
          have nodeMem := endpoints.2
          unfold drawingCarrierNodes at nodeMem
          simpa using nodeMem
        have keyEq :
            other.carrierKey = terminal.carrierKey := by
          rw [firstEq, otherEq] at common
          simpa [CarrierNode.carrierKey] using common.symm
        have carrierData :=
          segmentTerminals_indexed_translate_eq_of_carrierKey_eq
            graph otherMem terminalMem keyEq
        have carrierData' :
            other.indexed = indexed ∧
              other.translate = translate := by
          simpa [terminal] using carrierData
        have endpointNe : other.endpoint ≠ endpoint := by
          intro endpointEq
          apply endpointsNe
          rw [firstEq, otherEq]
          apply congrArg CarrierNode.terminal
          exact SegmentTerminal.eq_of_fields_eq
            carrierData'.1.symm carrierData'.2.symm endpointEq.symm
        have endpointEq :
            other.endpoint = endpoint.other :=
          SegmentEnd.eq_other_of_ne endpointNe
        have lower : terminal.IsLower := by
          by_contra notLower
          rw [if_neg notLower] at orientation
          exact endpointsNe (firstEq.trans orientation.symm)
        have lowerZero :
            (⟨indexed, (0, 0), endpoint⟩ :
              SegmentTerminal).IsLower :=
          by simpa [terminal, SegmentTerminal.IsLower] using lower
        simp [PeriodicEquality.normalizeLink,
          normalizeCarrierNode, terminalDirectNormalizedLink,
          firstEq, otherEq, carrierData'.1, carrierData'.2,
          endpointEq, lowerZero, Cell.sub]
  · cases otherEq : link.first with
    | boundary boundary =>
        simp [normalizedTerminalLinkClass,
          PeriodicEquality.normalizeLink,
          normalizeCarrierNode, periodicCarrierNodeClass,
          secondEq, otherEq] at classEq
    | terminal other =>
        have otherMem :
            other ∈ drawingSegmentTerminals graph := by
          rw [otherEq] at endpoints
          have nodeMem := endpoints.1
          unfold drawingCarrierNodes at nodeMem
          simpa using nodeMem
        have keyEq :
            other.carrierKey = terminal.carrierKey := by
          rw [otherEq, secondEq] at common
          simpa [CarrierNode.carrierKey] using common
        have carrierData :=
          segmentTerminals_indexed_translate_eq_of_carrierKey_eq
            graph otherMem terminalMem keyEq
        have carrierData' :
            other.indexed = indexed ∧
              other.translate = translate := by
          simpa [terminal] using carrierData
        have endpointNe : other.endpoint ≠ endpoint := by
          intro endpointEq
          apply endpointsNe
          rw [otherEq, secondEq]
          apply congrArg CarrierNode.terminal
          exact SegmentTerminal.eq_of_fields_eq
            carrierData'.1 carrierData'.2 endpointEq
        have endpointEq :
            other.endpoint = endpoint.other :=
          SegmentEnd.eq_other_of_ne endpointNe
        have notLower : ¬terminal.IsLower := by
          intro lower
          rw [if_pos lower] at orientation
          exact endpointsNe (orientation.trans secondEq.symm)
        have notLowerZero :
            ¬(⟨indexed, (0, 0), endpoint⟩ :
              SegmentTerminal).IsLower := by
          simpa [terminal, SegmentTerminal.IsLower] using notLower
        simp [PeriodicEquality.normalizeLink,
          normalizeCarrierNode, terminalDirectNormalizedLink,
          secondEq, otherEq, carrierData'.1, carrierData'.2,
          endpointEq, notLowerZero, Cell.sub]

theorem normalizedTerminalLinkClass_injective_on_incident
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd)
    {first second :
      PeriodicEquality.NormalizedLink PeriodicCarrierNode}
    (firstMem :
      first ∈
        (drawingCompleteCarrierLinks graph).map
          (PeriodicEquality.normalizeLink normalizeCarrierNode))
    (secondMem :
      second ∈
        (drawingCompleteCarrierLinks graph).map
          (PeriodicEquality.normalizeLink normalizeCarrierNode))
    (firstIncident :
      first.first = .terminal indexed endpoint ∨
        first.second = .terminal indexed endpoint)
    (secondIncident :
      second.first = .terminal indexed endpoint ∨
        second.second = .terminal indexed endpoint)
    (classEq :
      normalizedTerminalLinkClass
          (.terminal indexed endpoint) first =
        normalizedTerminalLinkClass
          (.terminal indexed endpoint) second) :
    first = second := by
  rcases List.mem_map.mp firstMem with
    ⟨firstSource, firstSourceMem, firstEq⟩
  rcases List.mem_map.mp secondMem with
    ⟨secondSource, secondSourceMem, secondEq⟩
  subst first
  subst second
  rcases (normalizedLink_incident_terminal_iff
    firstSource indexed endpoint).mp firstIncident with
    ⟨firstTranslate, firstSourceIncident⟩
  rcases (normalizedLink_incident_terminal_iff
    secondSource indexed endpoint).mp secondIncident with
    ⟨secondTranslate, secondSourceIncident⟩
  cases firstClass :
      normalizedTerminalLinkClass (.terminal indexed endpoint)
        (PeriodicEquality.normalizeLink
          normalizeCarrierNode firstSource) with
  | none =>
      have secondClass :
          normalizedTerminalLinkClass (.terminal indexed endpoint)
              (PeriodicEquality.normalizeLink
                normalizeCarrierNode secondSource) = none := by
        rw [← classEq]
        exact firstClass
      rw [normalizeLink_eq_terminalDirectNormalizedLink_of_class_none
        wellFormed degree isLocal indexed endpoint
          firstSourceMem firstIncident firstClass]
      rw [normalizeLink_eq_terminalDirectNormalizedLink_of_class_none
        wellFormed degree isLocal indexed endpoint
          secondSourceMem secondIncident secondClass]
  | some classTranslate =>
      have secondClass :
          normalizedTerminalLinkClass (.terminal indexed endpoint)
              (PeriodicEquality.normalizeLink
                normalizeCarrierNode secondSource) =
            some classTranslate := by
        rw [← classEq]
        exact firstClass
      have firstTranslateEq :=
        normalizedTerminalLinkClass_some_eq_terminal_translate
          graph indexed endpoint firstSourceMem
            firstTranslate classTranslate
            firstSourceIncident firstClass
      have secondTranslateEq :=
        normalizedTerminalLinkClass_some_eq_terminal_translate
          graph indexed endpoint secondSourceMem
            secondTranslate classTranslate
            secondSourceIncident secondClass
      have translatesEq :
          firstTranslate = secondTranslate :=
        firstTranslateEq.trans secondTranslateEq.symm
      let terminal : SegmentTerminal :=
        ⟨indexed, firstTranslate, endpoint⟩
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph :=
        drawingCompleteCarrierLink_terminal_mem
          graph firstSourceMem firstSourceIncident
      have firstChainMem :=
        drawingCompleteCarrierLink_mem_terminal_chain
          graph firstSourceMem firstSourceIncident
      have secondSourceIncident' :
          secondSource.first = .terminal terminal ∨
            secondSource.second = .terminal terminal := by
        simpa [terminal, translatesEq] using secondSourceIncident
      have secondChainMem :=
        drawingCompleteCarrierLink_mem_terminal_chain
          graph secondSourceMem secondSourceIncident'
      have sourcesEq :=
        completeCarrierLinks_eq_of_terminal_incident
          wellFormed degree isLocal terminalMem
            firstChainMem secondChainMem
            firstSourceIncident secondSourceIncident'
      rw [sourcesEq]

theorem normalizedCompleteCarrierLink_not_both_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd)
    {link : PeriodicEquality.NormalizedLink PeriodicCarrierNode}
    (linkMem :
      link ∈
        (drawingCompleteCarrierLinks graph).map
          (PeriodicEquality.normalizeLink normalizeCarrierNode)) :
    ¬(link.first = .terminal indexed endpoint ∧
      link.second = .terminal indexed endpoint) := by
  rcases List.mem_map.mp linkMem with
    ⟨source, sourceMem, sourceEq⟩
  subst link
  rintro ⟨firstEq, secondEq⟩
  rcases (normalizeLink_first_eq_terminal_iff
    source indexed endpoint).mp firstEq with
    ⟨firstTranslate, sourceFirstEq⟩
  rcases (normalizeLink_second_eq_terminal_iff
    source indexed endpoint).mp secondEq with
    ⟨secondTranslate, sourceSecondEq⟩
  have common :=
    drawingCompleteCarrierLinks_common_key graph sourceMem
  rw [sourceFirstEq, sourceSecondEq] at common
  have translatesEq : firstTranslate = secondTranslate := by
    simpa [CarrierNode.carrierKey,
      SegmentTerminal.carrierKey,
      PeriodicGridDrawing.SegmentOccurrenceKey] using
        congrArg (fun key => key.2.2) common
  exact drawingCompleteCarrierLink_endpoints_ne graph sourceMem
    (sourceFirstEq.trans
      ((congrArg CarrierNode.terminal
        (by simp [translatesEq])).trans sourceSecondEq.symm))

def normalizedLinkIncident
    {Variable : Type*} [DecidableEq Variable]
    (target : Variable)
    (link : PeriodicEquality.NormalizedLink Variable) : Bool :=
  decide (link.first = target ∨ link.second = target)

def deduplicatedNormalizedCompleteCarrierLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (PeriodicEquality.NormalizedLink PeriodicCarrierNode) :=
  ((drawingCompleteCarrierLinks graph).map
    (PeriodicEquality.normalizeLink normalizeCarrierNode)).dedup

@[simp]
theorem normalizedLinkIncident_eq_true_iff
    {Variable : Type*} [DecidableEq Variable]
    (target : Variable)
    (link : PeriodicEquality.NormalizedLink Variable) :
    normalizedLinkIncident target link = true ↔
      link.first = target ∨ link.second = target := by
  simp [normalizedLinkIncident]

theorem normalizedLinkEndpoints_count_eq_incident_length
    {Variable : Type*} [DecidableEq Variable]
    (links : List (PeriodicEquality.NormalizedLink Variable))
    (target : Variable)
    (notBoth :
      ∀ link ∈ links,
        ¬(link.first = target ∧ link.second = target)) :
    (PeriodicEquality.normalizedLinkEndpoints links).count target =
      (links.filter
        (normalizedLinkIncident target)).length := by
  unfold PeriodicEquality.normalizedLinkEndpoints
  induction links with
  | nil =>
      simp
  | cons link links induction =>
      have tailNotBoth :
          ∀ tailLink ∈ links,
            ¬(tailLink.first = target ∧
              tailLink.second = target) := by
        intro tailLink tailMem
        exact notBoth tailLink (by simp [tailMem])
      rw [List.flatMap_cons, List.count_append,
        List.filter_cons]
      rw [induction tailNotBoth]
      by_cases firstEq : link.first = target <;>
        by_cases secondEq : link.second = target
      · exact (notBoth link (by simp) ⟨firstEq, secondEq⟩).elim
      · simp [normalizedLinkIncident, firstEq, secondEq,
          Nat.add_comm]
      · simp [normalizedLinkIncident, firstEq, secondEq,
          Nat.add_comm]
      · simp [normalizedLinkIncident, firstEq, secondEq]

theorem deduplicatedNormalizedCompleteCarrierLinks_terminal_count_le_three
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (endpoint : SegmentEnd) :
    (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedCompleteCarrierLinks graph)).count
        (.terminal indexed endpoint) ≤ 3 := by
  let rawLinks :=
    (drawingCompleteCarrierLinks graph).map
      (PeriodicEquality.normalizeLink normalizeCarrierNode)
  let links := rawLinks.dedup
  let target : PeriodicCarrierNode :=
    .terminal indexed endpoint
  let incidentLinks :=
    links.filter (normalizedLinkIncident target)
  let classes : List (Option Cell) :=
    none ::
      (segmentCrossingTranslations graph indexed).toList.map some
  have linksNodup : links.Nodup :=
    List.nodup_dedup rawLinks
  have incidentNodup : incidentLinks.Nodup :=
    linksNodup.filter _
  have classNodup :
      (incidentLinks.map
        (normalizedTerminalLinkClass target)).Nodup := by
    apply incidentNodup.map_on
    intro first firstMem second secondMem classEq
    have firstData := List.mem_filter.mp firstMem
    have secondData := List.mem_filter.mp secondMem
    have firstRaw : first ∈ rawLinks := by
      simpa [links] using firstData.1
    have secondRaw : second ∈ rawLinks := by
      simpa [links] using secondData.1
    have firstIncident :
        first.first = target ∨ first.second = target :=
      (normalizedLinkIncident_eq_true_iff
        target first).mp firstData.2
    have secondIncident :
        second.first = target ∨ second.second = target :=
      (normalizedLinkIncident_eq_true_iff
        target second).mp secondData.2
    exact normalizedTerminalLinkClass_injective_on_incident
      wellFormed degree isLocal indexed endpoint
        firstRaw secondRaw firstIncident secondIncident classEq
  have classesNodup : classes.Nodup := by
    unfold classes
    apply List.Nodup.cons
    · simp
    · apply (segmentCrossingTranslations graph indexed).nodup_toList.map
      intro first second equal
      exact Option.some.inj equal
  have classSubset :
      (incidentLinks.map
        (normalizedTerminalLinkClass target)).toFinset ⊆
          classes.toFinset := by
    intro terminalClass terminalClassMem
    rcases List.mem_map.mp
      (List.mem_toFinset.mp terminalClassMem) with
      ⟨link, linkMem, classEq⟩
    subst terminalClass
    have linkData := List.mem_filter.mp linkMem
    have linkRaw : link ∈ rawLinks := by
      simpa [links] using linkData.1
    have linkIncident :
        link.first = target ∨ link.second = target :=
      (normalizedLinkIncident_eq_true_iff
        target link).mp linkData.2
    apply List.mem_toFinset.mpr
    change link ∈
      (drawingCompleteCarrierLinks graph).map
        (PeriodicEquality.normalizeLink normalizeCarrierNode) at linkRaw
    rcases List.mem_map.mp linkRaw with
      ⟨source, sourceMem, sourceEq⟩
    subst link
    change
      (PeriodicEquality.normalizeLink
          normalizeCarrierNode source).first =
            .terminal indexed endpoint ∨
        (PeriodicEquality.normalizeLink
          normalizeCarrierNode source).second =
            .terminal indexed endpoint at linkIncident
    have classMem :=
      normalizedTerminalLinkClass_mem
        graph indexed endpoint sourceMem linkIncident
    change normalizedTerminalLinkClass target
      (PeriodicEquality.normalizeLink
        normalizeCarrierNode source) ∈ classes at classMem
    exact classMem
  have classLengthLe :
      (incidentLinks.map
        (normalizedTerminalLinkClass target)).length ≤
          classes.length := by
    have cardLe := Finset.card_le_card classSubset
    rw [List.toFinset_card_of_nodup classNodup,
      List.toFinset_card_of_nodup classesNodup] at cardLe
    exact cardLe
  have incidentLengthLeThree :
      incidentLinks.length ≤ 3 := by
    rw [List.length_map] at classLengthLe
    have crossingCardLe :=
      segmentCrossingTranslations_card_le_two
        wellFormed degree isLocal indexedMem
    simp [classes] at classLengthLe
    omega
  change
    (PeriodicEquality.normalizedLinkEndpoints links).count
      target ≤ 3
  rw [normalizedLinkEndpoints_count_eq_incident_length
    links target]
  · exact incidentLengthLeThree
  · intro link linkMem
    have linkRaw : link ∈ rawLinks := by
      simpa [links] using linkMem
    exact normalizedCompleteCarrierLink_not_both_terminal
      graph indexed endpoint (by
        simpa [rawLinks] using linkRaw)

def deduplicatedNormalizedCompleteCarrierFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    PeriodicCNF PeriodicCarrierNode :=
  PeriodicEquality.deduplicatedNormalizedFormula
    normalizeCarrierNode (drawingCompleteCarrierLinks graph)

/-- After periodic normalization and clause deduplication, complete straight
carrier equalities use a terminal prototype at most six times. -/
theorem deduplicatedNormalizedCompleteCarrierFormula_terminal_count_le_six
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (endpoint : SegmentEnd) :
    (deduplicatedNormalizedCompleteCarrierFormula graph).variableOccurrences.count
      (.terminal indexed endpoint) ≤ 6 := by
  unfold deduplicatedNormalizedCompleteCarrierFormula
  rw [PeriodicEquality.deduplicatedNormalizedFormula_occurrence_count]
  change
    2 * (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedCompleteCarrierLinks graph)).count
        (.terminal indexed endpoint) ≤ 6
  have endpointDegree :=
    deduplicatedNormalizedCompleteCarrierLinks_terminal_count_le_three
      wellFormed degree isLocal indexedMem endpoint
  omega

end PeriodicOrthocrossing
end LeanTrominoes
