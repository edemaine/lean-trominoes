/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarClauseNormalizationDegree

/-!
# Periodically normalized central-atom degree

This module injects normalized active variable arms into source-incidence
indices and transfers the source formula's three-occurrence bound.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Recover the tagged metadata incidence that generated a represented routed
occurrence. -/
theorem CNFRouteOccurrence.taggedIncidence_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    (occurrence.incidence, occurrence.edgeIndex) ∈
      (PeriodicCNF.incidencesWithMetadata formula).zipIdx := by
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem, translatedMem⟩
  rcases List.mem_map.mp translatedMem with
    ⟨translate, _translateMem, occurrenceEq⟩
  subst occurrence
  exact taggedIncidenceMem

/-- Equal incidence metadata and route indices give equal target terminal
prototypes, regardless of explicit route translation. -/
theorem CNFRouteOccurrence.targetTerminal_indexed_eq_of_data_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : CNFRouteOccurrence Variable}
    (incidenceEq : first.incidence = second.incidence)
    (edgeIndexEq : first.edgeIndex = second.edgeIndex) :
    (first.targetTerminal formula).indexed =
      (second.targetTerminal formula).indexed := by
  rcases first with
    ⟨firstIncidence, firstEdgeIndex, firstTranslate⟩
  rcases second with
    ⟨secondIncidence, secondEdgeIndex, secondTranslate⟩
  simp only at incidenceEq edgeIndexEq
  subst secondIncidence
  subst secondEdgeIndex
  rfl

/-- Read the terminal route index from a normalized active variable arm. -/
def normalizedRoutedVariableLinkRouteIndex
    {Variable : Type*}
    (link : PeriodicEquality.NormalizedLink
      (PeriodicPlanarSATVariable Variable)) : Nat :=
  match link.first with
  | .terminal indexed _ => indexed.routeIndex
  | _ => 0

/-- On raw normalized active arms, the route-index classifier is injective. -/
theorem normalizedRoutedVariableLink_eq_of_routeIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second :
      PeriodicEquality.NormalizedLink
        (PeriodicPlanarSATVariable Variable)}
    (firstMem :
      first ∈
        (drawingRoutedVariableLinks formula).map
          (PeriodicEquality.normalizeLink
            (normalizePlanarSATNode
              (PeriodicCNF.incidenceGraph formula))))
    (secondMem :
      second ∈
        (drawingRoutedVariableLinks formula).map
          (PeriodicEquality.normalizeLink
            (normalizePlanarSATNode
              (PeriodicCNF.incidenceGraph formula))))
    (routeIndexEq :
      normalizedRoutedVariableLinkRouteIndex first =
        normalizedRoutedVariableLinkRouteIndex second) :
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
  rw [firstNormalized, secondNormalized] at routeIndexEq
  change firstOccurrence.edgeIndex =
    secondOccurrence.edgeIndex at routeIndexEq
  have incidenceEq :=
    CNFRouteOccurrence.incidence_eq_of_edgeIndex_eq
      formula firstOccurrenceMem secondOccurrenceMem routeIndexEq
  have targetIndexedEq :=
    CNFRouteOccurrence.targetTerminal_indexed_eq_of_data_eq
      formula incidenceEq routeIndexEq
  have routeEdgeEq :
      firstOccurrence.edge = secondOccurrence.edge :=
    congrArg CNFIncidence.edge incidenceEq
  rw [firstNormalized, secondNormalized,
    targetIndexedEq, incidenceEq, routeEdgeEq]

/-- Global incidence indices whose source literals use one fixed atom. -/
def sourceIncidenceRouteIndices
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (atom : Variable) :
    List Nat :=
  (((PeriodicCNF.incidencesWithMetadata formula).zipIdx.filter
    fun taggedIncidence =>
      taggedIncidence.1.literal.atom = atom).map Prod.snd)

theorem sourceIncidenceRouteIndices_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (atom : Variable) :
    (sourceIncidenceRouteIndices formula atom).Nodup := by
  unfold sourceIncidenceRouteIndices
  have filteredNodup :=
    ((List.nodup_zipIdx_map_snd
      (PeriodicCNF.incidencesWithMetadata formula)).of_map
        Prod.snd).filter
          (fun taggedIncidence =>
            taggedIncidence.1.literal.atom = atom)
  apply filteredNodup.map_on
  intro first firstMem second secondMem indexEq
  exact tagged_eq_of_mem_zipIdx_of_snd_eq
    (List.mem_filter.mp firstMem).1
    (List.mem_filter.mp secondMem).1 indexEq

theorem zipIdx_filter_fst_length
    {Value : Type*} (predicate : Value → Bool) :
    ∀ (values : List Value) (startIndex : Nat),
      ((values.zipIdx startIndex).filter
        fun tagged => predicate tagged.1).length =
          (values.filter predicate).length := by
  intro values
  induction values with
  | nil =>
      simp
  | cons value values induction =>
      intro startIndex
      simp only [List.zipIdx, List.filter_cons]
      by_cases selected : predicate value = true
      · simp [selected, induction (startIndex + 1)]
      · simp [selected, induction (startIndex + 1)]

theorem sourceIncidenceRouteIndices_length
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (atom : Variable) :
    (sourceIncidenceRouteIndices formula atom).length =
      formula.variableOccurrences.count atom := by
  rw [← PeriodicCNF.incidencesWithMetadata_literal_atoms formula]
  unfold sourceIncidenceRouteIndices
  rw [List.length_map,
    zipIdx_filter_fst_length
      (fun incidence : CNFIncidence Variable =>
        decide (incidence.literal.atom = atom))]
  rw [List.count_eq_length_filter]
  induction (PeriodicCNF.incidencesWithMetadata formula) with
  | nil =>
      simp
  | cons incidence incidences induction =>
      by_cases selected : incidence.literal.atom = atom
      · simp [selected, induction]
      · simp [selected, induction]

/-- Under the source occurrence bound, the deduplicated normalized active
arms have atom endpoint degree at most three. -/
theorem
    deduplicatedNormalizedRoutedVariableLinks_atom_count_le_three
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (occurrences : formula.OccurrencesAtMost 3)
    (atom : Variable) :
    (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRoutedVariableLinks formula)).count
        (.atom atom) ≤ 3 := by
  let rawLinks :=
    (drawingRoutedVariableLinks formula).map
      (PeriodicEquality.normalizeLink
        (normalizePlanarSATNode
          (PeriodicCNF.incidenceGraph formula)))
  let links := rawLinks.dedup
  let target : PeriodicPlanarSATVariable Variable := .atom atom
  let incidentLinks :=
    links.filter (normalizedLinkIncident target)
  let sourceIndices := sourceIncidenceRouteIndices formula atom
  have linksNodup : links.Nodup :=
    List.nodup_dedup rawLinks
  have incidentNodup : incidentLinks.Nodup :=
    linksNodup.filter _
  have classifiedNodup :
      (incidentLinks.map
        normalizedRoutedVariableLinkRouteIndex).Nodup := by
    apply incidentNodup.map_on
    intro first firstMem second secondMem routeIndexEq
    have firstRaw : first ∈ rawLinks := by
      have firstLinkMem := (List.mem_filter.mp firstMem).1
      simpa [links] using firstLinkMem
    have secondRaw : second ∈ rawLinks := by
      have secondLinkMem := (List.mem_filter.mp secondMem).1
      simpa [links] using secondLinkMem
    exact normalizedRoutedVariableLink_eq_of_routeIndex_eq
      formula firstRaw secondRaw routeIndexEq
  have sourceIndicesNodup : sourceIndices.Nodup :=
    sourceIncidenceRouteIndices_nodup formula atom
  have classifiedSubset :
      (incidentLinks.map
        normalizedRoutedVariableLinkRouteIndex).toFinset ⊆
          sourceIndices.toFinset := by
    intro routeIndex routeIndexMem
    rcases List.mem_map.mp
      (List.mem_toFinset.mp routeIndexMem) with
      ⟨link, linkMem, routeIndexEq⟩
    have linkData := List.mem_filter.mp linkMem
    have linkRaw : link ∈ rawLinks := by
      simpa [links] using linkData.1
    have linkIncident :
        link.first = target ∨ link.second = target :=
      (normalizedLinkIncident_eq_true_iff
        target link).mp linkData.2
    rcases List.mem_map.mp linkRaw with
      ⟨source, sourceMem, linkEq⟩
    rcases drawingRoutedVariableLink_witness
      formula sourceMem with
        ⟨site, occurrence, occurrenceMem, siteEq,
          sourceFirst, sourceSecond⟩
    subst link
    have normalized :=
      normalizeRoutedVariableLink_eq_of_witness
        formula siteEq sourceFirst sourceSecond
    rw [normalized] at linkIncident routeIndexEq
    have atomEq :
        occurrence.incidence.literal.atom = atom := by
      rcases linkIncident with linkIncident | linkIncident
      · simp at linkIncident
      · exact
          PeriodicPlanarSATVariable.atom.inj linkIncident
    have taggedMem :=
      occurrence.taggedIncidence_mem formula occurrenceMem
    apply List.mem_toFinset.mpr
    change occurrence.edgeIndex = routeIndex at routeIndexEq
    rw [← routeIndexEq]
    unfold sourceIndices sourceIncidenceRouteIndices
    apply List.mem_map.mpr
    exact
      ⟨(occurrence.incidence, occurrence.edgeIndex),
        List.mem_filter.mpr ⟨taggedMem, by simp [atomEq]⟩, rfl⟩
  have classifiedLengthLe :
      (incidentLinks.map
        normalizedRoutedVariableLinkRouteIndex).length ≤
          sourceIndices.length := by
    have cardLe := Finset.card_le_card classifiedSubset
    rw [List.toFinset_card_of_nodup classifiedNodup,
      List.toFinset_card_of_nodup sourceIndicesNodup] at cardLe
    exact cardLe
  have incidentLengthLeThree :
      incidentLinks.length ≤ 3 := by
    rw [List.length_map,
      sourceIncidenceRouteIndices_length] at classifiedLengthLe
    exact classifiedLengthLe.trans (occurrences atom)
  change
    (PeriodicEquality.normalizedLinkEndpoints links).count
      target ≤ 3
  rw [normalizedLinkEndpoints_count_eq_incident_length
    links target]
  · exact incidentLengthLeThree
  · intro link linkMem
    have linkRaw : link ∈ rawLinks := by
      simpa [links] using linkMem
    rcases List.mem_map.mp linkRaw with
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

/-- Central atoms occur in at most two implication literals per normalized
active arm and have at most three distinct arms. -/
theorem
    deduplicatedNormalizedRoutedVariableFormula_atom_count_le_six
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (occurrences : formula.OccurrencesAtMost 3)
    (atom : Variable) :
    (deduplicatedNormalizedRoutedVariableFormula
      formula).variableOccurrences.count (.atom atom) ≤ 6 := by
  unfold deduplicatedNormalizedRoutedVariableFormula
  rw [PeriodicEquality.deduplicatedNormalizedFormula_occurrence_count]
  change
    2 * (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRoutedVariableLinks formula)).count
        (.atom atom) ≤ 6
  have endpointDegree :=
    deduplicatedNormalizedRoutedVariableLinks_atom_count_le_three
      occurrences atom
  omega

/-- Route wires and routed source clauses contain no central atom
prototypes. -/
theorem normalizedExternalPlanarSATFormula_atom_count_le_six
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (occurrences : formula.OccurrencesAtMost 3)
    (atom : Variable) :
    (normalizedExternalPlanarSATFormula
      formula).variableOccurrences.count (.atom atom) ≤ 6 := by
  have variableLe :=
    deduplicatedNormalizedRoutedVariableFormula_atom_count_le_six
      occurrences atom
  have carrierZero :
      (embedPeriodicCarrierFormula
        (Variable := Variable)
        (normalizedRouteWireFormula
          (PeriodicCNF.incidenceGraph formula))).variableOccurrences.count
            (.atom atom) = 0 := by
    apply List.count_eq_zero_of_not_mem
    rw [embedPeriodicCarrierFormula_variableOccurrences]
    intro atomMem
    rcases List.mem_map.mp atomMem with
      ⟨carrierNode, _carrierNodeMem, carrierNodeEq⟩
    cases carrierNode <;>
      simp [periodicCarrierNodeToPlanarSATVariable] at carrierNodeEq
  have clauseZero :
      (deduplicatedNormalizedRoutedClauseFormula
        formula).variableOccurrences.count (.atom atom) = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro atomMem
    rcases List.mem_flatMap.mp atomMem with
      ⟨clause, clauseMem, atomMem⟩
    have clauseRaw :
        clause ∈ normalizedRoutedClauseClauses formula :=
      List.mem_dedup.mp clauseMem
    rcases normalizedRoutedClause_mem_witness
      formula clauseRaw with
        ⟨site, _siteMem, clauseEq⟩
    rw [clauseEq] at atomMem
    rcases List.mem_map.mp atomMem with
      ⟨literal, literalMem, atomEq⟩
    rcases List.mem_map.mp literalMem with
      ⟨taggedIncidence, _taggedMem, literalEq⟩
    have impossible :
        (routedSourcePeriodicLiteral
          formula (0, 0) taggedIncidence).atom = .atom atom :=
      (congrArg PeriodicLiteral.atom literalEq).trans atomEq
    simp [routedSourcePeriodicLiteral] at impossible
  unfold normalizedExternalPlanarSATFormula
    PeriodicCNF.variableOccurrences
  rw [List.flatMap_append, List.flatMap_append,
    List.count_append, List.count_append]
  unfold PeriodicCNF.variableOccurrences at carrierZero clauseZero variableLe
  omega

end PeriodicOrthocrossing
end LeanTrominoes
