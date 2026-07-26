import LeanTrominoes.PeriodicOrthocrossingRouteEndpointNormalizationDegree
import LeanTrominoes.PeriodicCNFPlanarPeriodicization
import LeanTrominoes.PeriodicEqualityNormalization

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Periodic normalization of the external routed SAT nodes. -/
def normalizePlanarSATNode
    {Variable : Type*}
    (node : PlanarSATNode Variable) :
    PeriodicPlanarSATVariable Variable × Cell :=
  normalizePlanarSATVariable (.inl node)

@[simp]
theorem normalizePlanarSATNode_terminal
    {Variable : Type*} (terminal : SegmentTerminal) :
    (normalizePlanarSATNode
        (PlanarSATNode.carrier (.terminal terminal)) :
      PeriodicPlanarSATVariable Variable × Cell) =
        (.terminal terminal.indexed terminal.endpoint,
          terminal.translate) := rfl

@[simp]
theorem normalizePlanarSATNode_boundary
    {Variable : Type*} (boundary : CrossingBoundary) :
    (normalizePlanarSATNode
        (PlanarSATNode.carrier (.boundary boundary)) :
      PeriodicPlanarSATVariable Variable × Cell) =
        (.boundary boundary, (0, 0)) := rfl

@[simp]
theorem normalizePlanarSATNode_atom
    {Variable : Type*} (atom : Variable) (translate : Cell) :
    normalizePlanarSATNode (.atom (atom, translate)) =
      (.atom atom, translate) := rfl

/-- Two represented route occurrences with the same global edge index have
the same incidence metadata, even if their explicit translations differ. -/
theorem CNFRouteOccurrence.incidence_eq_of_edgeIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : CNFRouteOccurrence Variable}
    (firstMem : first ∈ drawingCNFRouteOccurrences formula)
    (secondMem : second ∈ drawingCNFRouteOccurrences formula)
    (edgeIndexEq : first.edgeIndex = second.edgeIndex) :
    first.incidence = second.incidence := by
  rcases List.mem_flatMap.mp firstMem with
    ⟨firstTagged, firstTaggedMem, firstTranslateMem⟩
  rcases List.mem_map.mp firstTranslateMem with
    ⟨firstTranslate, _firstTranslateMem, firstEq⟩
  rcases List.mem_flatMap.mp secondMem with
    ⟨secondTagged, secondTaggedMem, secondTranslateMem⟩
  rcases List.mem_map.mp secondTranslateMem with
    ⟨secondTranslate, _secondTranslateMem, secondEq⟩
  subst first
  subst second
  have taggedEq :
      firstTagged = secondTagged :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstTaggedMem secondTaggedMem edgeIndexEq
  exact congrArg (fun tagged => tagged.1) taggedEq

/-- Every active variable-arm link comes from a represented routed
occurrence reaching the arm's variable site. -/
theorem drawingRoutedVariableLink_witness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ drawingRoutedVariableLinks formula) :
    ∃ site occurrence,
      occurrence ∈ drawingCNFRouteOccurrences formula ∧
      occurrence.variableOccurrence = site ∧
      link.first =
        .carrier (.terminal (occurrence.targetTerminal formula)) ∧
      link.second = .atom site := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨site, _siteMem, linkMem⟩
  rcases List.mem_map.mp linkMem with
    ⟨taggedNode, taggedNodeMem, linkEq⟩
  have nodeMemTake :
      taggedNode.1 ∈
        (routedVariableNodes formula site).take 3 :=
    List.fst_mem_of_mem_zipIdx taggedNodeMem
  have nodeMem :
      taggedNode.1 ∈ routedVariableNodes formula site :=
    List.mem_of_mem_take nodeMemTake
  rcases (mem_routedVariableNodes_iff
      formula site taggedNode.1).mp nodeMem with
    ⟨occurrence, occurrenceMem, nodeEq⟩
  have occurrenceData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMem
  refine ⟨site, occurrence, occurrenceData.1,
    occurrenceData.2, ?_, ?_⟩
  · subst link
    exact nodeEq
  · subst link
    rfl

/-- A variable-arm link's periodic normalization depends on its routed
incidence but not on the explicit neighboring translation. -/
theorem normalizeRoutedVariableLink_eq_of_witness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    {site : VariableRouteSite Variable}
    {occurrence : CNFRouteOccurrence Variable}
    (siteEq : occurrence.variableOccurrence = site)
    (firstEq :
      link.first =
        .carrier (.terminal (occurrence.targetTerminal formula)))
    (secondEq : link.second = .atom site) :
    PeriodicEquality.normalizeLink normalizePlanarSATNode link =
      ⟨.terminal (occurrence.targetTerminal formula).indexed .finish,
        .atom occurrence.incidence.literal.atom,
        occurrence.edge.offset⟩ := by
  rcases occurrence with
    ⟨incidence, edgeIndex, translate⟩
  subst site
  rcases link with ⟨first, second, positions⟩
  simp only at firstEq secondEq
  subst first
  subst second
  simp [PeriodicEquality.normalizeLink,
    normalizePlanarSATNode, normalizePlanarSATVariable,
    CNFRouteOccurrence.targetTerminal,
    CNFRouteOccurrence.variableOccurrence,
    CNFRouteOccurrence.edge, Cell.add, Cell.sub]

/-- Normalized variable-arm links incident to one target terminal prototype
are identical. -/
theorem normalizedDrawingRoutedVariableLink_eq_of_terminal_incident
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment)
    {first second :
      PeriodicEquality.NormalizedLink
        (PeriodicPlanarSATVariable Variable)}
    (firstMem :
      first ∈
        (drawingRoutedVariableLinks formula).map
          (PeriodicEquality.normalizeLink normalizePlanarSATNode))
    (secondMem :
      second ∈
        (drawingRoutedVariableLinks formula).map
          (PeriodicEquality.normalizeLink normalizePlanarSATNode))
    (firstIncident :
      first.first = .terminal indexed .finish ∨
        first.second = .terminal indexed .finish)
    (secondIncident :
      second.first = .terminal indexed .finish ∨
        second.second = .terminal indexed .finish) :
    first = second := by
  rcases List.mem_map.mp firstMem with
    ⟨firstSource, firstSourceMem, firstEq⟩
  rcases drawingRoutedVariableLink_witness
    formula firstSourceMem with
      ⟨firstSite, firstOccurrence, firstOccurrenceMem,
        firstSiteEq, firstSourceFirst, firstSourceSecond⟩
  rcases List.mem_map.mp secondMem with
    ⟨secondSource, secondSourceMem, secondEq⟩
  rcases drawingRoutedVariableLink_witness
    formula secondSourceMem with
      ⟨secondSite, secondOccurrence, secondOccurrenceMem,
        secondSiteEq, secondSourceFirst, secondSourceSecond⟩
  subst first
  subst second
  have firstNormalized :=
    normalizeRoutedVariableLink_eq_of_witness
      formula firstSiteEq firstSourceFirst firstSourceSecond
  have secondNormalized :=
    normalizeRoutedVariableLink_eq_of_witness
      formula secondSiteEq secondSourceFirst secondSourceSecond
  rw [firstNormalized] at firstIncident
  rw [secondNormalized] at secondIncident
  have firstTargetEq :
      (firstOccurrence.targetTerminal formula).indexed = indexed := by
    rcases firstIncident with firstIncident | firstIncident
    · exact
        (PeriodicPlanarSATVariable.terminal.inj firstIncident).1
    · simp at firstIncident
  have secondTargetEq :
      (secondOccurrence.targetTerminal formula).indexed = indexed := by
    rcases secondIncident with secondIncident | secondIncident
    · exact
        (PeriodicPlanarSATVariable.terminal.inj secondIncident).1
    · simp at secondIncident
  have edgeIndexEq :
      firstOccurrence.edgeIndex = secondOccurrence.edgeIndex := by
    exact
      (congrArg IndexedGridSegment.routeIndex firstTargetEq).trans
        (congrArg IndexedGridSegment.routeIndex secondTargetEq).symm
  have incidenceEq :=
    CNFRouteOccurrence.incidence_eq_of_edgeIndex_eq
      formula firstOccurrenceMem secondOccurrenceMem edgeIndexEq
  have targetIndexedEq :
      (firstOccurrence.targetTerminal formula).indexed =
      (secondOccurrence.targetTerminal formula).indexed :=
    firstTargetEq.trans secondTargetEq.symm
  have routeEdgeEq :
      firstOccurrence.edge = secondOccurrence.edge :=
    congrArg CNFIncidence.edge incidenceEq
  rw [firstNormalized, secondNormalized]
  rw [targetIndexedEq, incidenceEq, routeEdgeEq]

/-- A normalized active variable arm cannot use one terminal prototype at
both ends: the other end is a central atom. -/
theorem normalizedRoutedVariableLink_not_both_terminal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment)
    {link :
      PeriodicEquality.NormalizedLink
        (PeriodicPlanarSATVariable Variable)}
    (linkMem :
      link ∈
        (drawingRoutedVariableLinks formula).map
          (PeriodicEquality.normalizeLink normalizePlanarSATNode)) :
    ¬(link.first = .terminal indexed .finish ∧
      link.second = .terminal indexed .finish) := by
  rcases List.mem_map.mp linkMem with
    ⟨source, sourceMem, linkEq⟩
  rcases drawingRoutedVariableLink_witness
    formula sourceMem with
      ⟨site, occurrence, _occurrenceMem, siteEq,
        sourceFirst, sourceSecond⟩
  subst link
  have normalized :=
    normalizeRoutedVariableLink_eq_of_witness
      formula siteEq sourceFirst sourceSecond
  rw [normalized]
  simp

/-- Active variable-arm links after periodic endpoint normalization and link
deduplication. -/
def deduplicatedNormalizedRoutedVariableLinks
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicEquality.NormalizedLink
      (PeriodicPlanarSATVariable Variable)) :=
  ((drawingRoutedVariableLinks formula).map
    (PeriodicEquality.normalizeLink normalizePlanarSATNode)).dedup

/-- Every target terminal prototype is incident to at most one normalized
active variable arm. -/
theorem
    deduplicatedNormalizedRoutedVariableLinks_terminal_count_le_one
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment) :
    (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRoutedVariableLinks formula)).count
        (.terminal indexed .finish) ≤ 1 := by
  let rawLinks :=
    (drawingRoutedVariableLinks formula).map
      (PeriodicEquality.normalizeLink normalizePlanarSATNode)
  let links := rawLinks.dedup
  let target : PeriodicPlanarSATVariable Variable :=
    .terminal indexed .finish
  let incidentLinks :=
    links.filter (normalizedLinkIncident target)
  have linksNodup : links.Nodup :=
    List.nodup_dedup rawLinks
  have incidentNodup : incidentLinks.Nodup :=
    linksNodup.filter _
  have incidentLengthLeOne :
      incidentLinks.length ≤ 1 := by
    cases incidentEq : incidentLinks with
    | nil =>
        simp
    | cons first rest =>
        have consNodup : (first :: rest).Nodup := by
          rw [incidentEq] at incidentNodup
          exact incidentNodup
        apply length_le_one_of_nodup_of_forall_eq
          consNodup first
        intro link linkMem
        have firstIncidentMem : first ∈ incidentLinks := by
          rw [incidentEq]
          simp
        have linkIncidentMem : link ∈ incidentLinks := by
          rw [incidentEq]
          exact linkMem
        have firstMem : first ∈ links :=
          (List.mem_filter.mp firstIncidentMem).1
        have linkMem' : link ∈ links :=
          (List.mem_filter.mp linkIncidentMem).1
        have firstRaw : first ∈ rawLinks := by
          simpa [links] using firstMem
        have linkRaw : link ∈ rawLinks := by
          simpa [links] using linkMem'
        have firstIncident :
            first.first = target ∨ first.second = target :=
          (normalizedLinkIncident_eq_true_iff
            target first).mp
              (List.mem_filter.mp firstIncidentMem).2
        have linkIncident :
            link.first = target ∨ link.second = target :=
          (normalizedLinkIncident_eq_true_iff
            target link).mp
              (List.mem_filter.mp linkIncidentMem).2
        exact
          normalizedDrawingRoutedVariableLink_eq_of_terminal_incident
            formula indexed linkRaw firstRaw
              linkIncident firstIncident
  change
    (PeriodicEquality.normalizedLinkEndpoints links).count
      target ≤ 1
  rw [normalizedLinkEndpoints_count_eq_incident_length
    links target]
  · exact incidentLengthLeOne
  · intro link linkMem
    have linkRaw : link ∈ rawLinks := by
      simpa [links] using linkMem
    exact normalizedRoutedVariableLink_not_both_terminal
      formula indexed (by
        simpa [rawLinks] using linkRaw)

def deduplicatedNormalizedRoutedVariableFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (PeriodicPlanarSATVariable Variable) :=
  PeriodicEquality.deduplicatedNormalizedFormula
    normalizePlanarSATNode (drawingRoutedVariableLinks formula)

/-- Periodic normalization and clause deduplication leave at most the two
implication literals of one active arm at each target terminal prototype. -/
theorem
    deduplicatedNormalizedRoutedVariableFormula_terminal_count_le_two
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment) :
    (deduplicatedNormalizedRoutedVariableFormula
      formula).variableOccurrences.count
        (.terminal indexed .finish) ≤ 2 := by
  unfold deduplicatedNormalizedRoutedVariableFormula
  rw [PeriodicEquality.deduplicatedNormalizedFormula_occurrence_count]
  change
    2 * (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRoutedVariableLinks formula)).count
        (.terminal indexed .finish) ≤ 2
  have endpointDegree :=
    deduplicatedNormalizedRoutedVariableLinks_terminal_count_le_one
      formula indexed
  omega

/-- Embed normalized carrier prototypes into the complete periodic planar
SAT variable type. -/
def periodicCarrierNodeToPlanarSATVariable
    {Variable : Type*} :
    PeriodicCarrierNode → PeriodicPlanarSATVariable Variable
  | .terminal indexed endpoint => .terminal indexed endpoint
  | .boundary boundary => .boundary boundary

theorem periodicCarrierNodeToPlanarSATVariable_injective
    {Variable : Type*} :
    Function.Injective
      (@periodicCarrierNodeToPlanarSATVariable Variable) := by
  intro first second equal
  cases first <;> cases second <;>
    simp [periodicCarrierNodeToPlanarSATVariable] at equal ⊢
  all_goals exact equal

/-- Rename a normalized carrier-only periodic formula into the complete
periodic planar SAT variable type. -/
def embedPeriodicCarrierFormula
    {Variable : Type*}
    (source : PeriodicCNF PeriodicCarrierNode) :
    PeriodicCNF (PeriodicPlanarSATVariable Variable) :=
  ⟨source.clauses.map fun clause =>
    clause.map fun literal =>
      ⟨periodicCarrierNodeToPlanarSATVariable literal.atom,
        literal.offset, literal.value⟩⟩

theorem embedPeriodicCarrierFormula_variableOccurrences
    {Variable : Type*}
    (source : PeriodicCNF PeriodicCarrierNode) :
    (embedPeriodicCarrierFormula
      (Variable := Variable) source).variableOccurrences =
        source.variableOccurrences.map
          periodicCarrierNodeToPlanarSATVariable := by
  simp [embedPeriodicCarrierFormula,
    PeriodicCNF.variableOccurrences,
    List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem embedPeriodicCarrierFormula_terminal_count
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF PeriodicCarrierNode)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    (embedPeriodicCarrierFormula
      (Variable := Variable) source).variableOccurrences.count
        (.terminal indexed endpoint) =
      source.variableOccurrences.count
        (.terminal indexed endpoint) := by
  rw [embedPeriodicCarrierFormula_variableOccurrences]
  exact
    List.count_map_of_injective
      source.variableOccurrences
      periodicCarrierNodeToPlanarSATVariable
      periodicCarrierNodeToPlanarSATVariable_injective
      (.terminal indexed endpoint)

/-- The periodically normalized route wire followed by the periodically
normalized active variable arms. -/
def normalizedRouteWireAndVariableFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (PeriodicPlanarSATVariable Variable) :=
  ⟨(embedPeriodicCarrierFormula
      (Variable := Variable)
      (normalizedRouteWireFormula
        (PeriodicCNF.incidenceGraph formula))).clauses ++
    (deduplicatedNormalizedRoutedVariableFormula formula).clauses⟩

/-- A routed target terminal has at most six normalized route-wire
occurrences and two normalized active-arm occurrences, meeting the final
degree-eight budget. -/
theorem
    normalizedRouteWireAndVariableFormula_targetTerminal_count_le_eight
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
    (normalizedRouteWireAndVariableFormula
      formula).variableOccurrences.count
        (.terminal
          (occurrence.targetTerminal formula).indexed .finish) ≤ 8 := by
  have routeLe :=
    normalizedRouteWireFormula_targetTerminal_count_le_six
      wellFormed degree isLocal occurrenceMem
  have embeddedRouteLe :
      (embedPeriodicCarrierFormula
        (Variable := Variable)
        (normalizedRouteWireFormula
          (PeriodicCNF.incidenceGraph formula))).variableOccurrences.count
            (.terminal
              (occurrence.targetTerminal formula).indexed .finish) ≤ 6 := by
    rw [embedPeriodicCarrierFormula_terminal_count]
    exact routeLe
  have variableLe :=
    deduplicatedNormalizedRoutedVariableFormula_terminal_count_le_two
      formula (occurrence.targetTerminal formula).indexed
  unfold normalizedRouteWireAndVariableFormula
    PeriodicCNF.variableOccurrences
  rw [List.flatMap_append, List.count_append]
  unfold PeriodicCNF.variableOccurrences at embeddedRouteLe
  unfold PeriodicCNF.variableOccurrences at variableLe
  omega

end PeriodicOrthocrossing
end LeanTrominoes
