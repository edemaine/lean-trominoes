/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRoutedClauseNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierNormalizedFamilyNodup
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierPortGeometry

/-! # Straight-carrier clauses are disjoint from routed source clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- If the first endpoint of a wrapped normalized carrier link is a routed
start terminal, then the physical endpoint itself is a start terminal. -/
theorem retainedCarrierLink_first_eq_terminal_start_of_normalized
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    {indexed : IndexedGridSegment}
    (normalizedEq :
      (PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization source) link).first.original =
          PeriodicPlanarSATVariable.terminal indexed .start) :
    ∃ terminal, link.first = .terminal terminal ∧
      terminal.endpoint = .start := by
  have underlyingEq :
      (@periodicCarrierNodeToPlanarSATVariable Variable)
          (PeriodicEquality.normalizeLink
            (normalizeCarrierNode source.incidenceGraph) link).first =
        (@PeriodicPlanarSATVariable.terminal Variable indexed .start) := by
    simpa using normalizedEq
  change (@periodicCarrierNodeToPlanarSATVariable Variable
      (normalizeCarrierNode source.incidenceGraph link.first).1) =
    PeriodicPlanarSATVariable.terminal indexed .start at underlyingEq
  cases firstNodeEq : link.first with
  | boundary boundary =>
      rw [firstNodeEq] at underlyingEq
      change PeriodicPlanarSATVariable.boundary
          (boundary.periodNormalize source.incidenceGraph) =
        PeriodicPlanarSATVariable.terminal indexed .start at underlyingEq
      cases underlyingEq
  | terminal terminal =>
      refine ⟨terminal, rfl, ?_⟩
      rw [firstNodeEq] at underlyingEq
      change PeriodicPlanarSATVariable.terminal
          terminal.indexed terminal.endpoint =
        PeriodicPlanarSATVariable.terminal indexed .start at underlyingEq
      exact (PeriodicPlanarSATVariable.terminal.inj underlyingEq).2

/-- If the second endpoint of a wrapped normalized carrier link is a routed
start terminal, then the physical endpoint itself is a start terminal. -/
theorem retainedCarrierLink_second_eq_terminal_start_of_normalized
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    {indexed : IndexedGridSegment}
    (normalizedEq :
      (PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization source) link).second.original =
          PeriodicPlanarSATVariable.terminal indexed .start) :
    ∃ terminal, link.second = .terminal terminal ∧
      terminal.endpoint = .start := by
  have underlyingEq :
      (@periodicCarrierNodeToPlanarSATVariable Variable)
          (PeriodicEquality.normalizeLink
            (normalizeCarrierNode source.incidenceGraph) link).second =
        (@PeriodicPlanarSATVariable.terminal Variable indexed .start) := by
    simpa using normalizedEq
  change (@periodicCarrierNodeToPlanarSATVariable Variable
      (normalizeCarrierNode source.incidenceGraph link.second).1) =
    PeriodicPlanarSATVariable.terminal indexed .start at underlyingEq
  cases secondNodeEq : link.second with
  | boundary boundary =>
      rw [secondNodeEq] at underlyingEq
      change PeriodicPlanarSATVariable.boundary
          (boundary.periodNormalize source.incidenceGraph) =
        PeriodicPlanarSATVariable.terminal indexed .start at underlyingEq
      cases underlyingEq
  | terminal terminal =>
      refine ⟨terminal, rfl, ?_⟩
      rw [secondNodeEq] at underlyingEq
      change PeriodicPlanarSATVariable.terminal
          terminal.indexed terminal.endpoint =
        PeriodicPlanarSATVariable.terminal indexed .start at underlyingEq
      exact (PeriodicPlanarSATVariable.terminal.inj underlyingEq).2

/-- No normalized retained straight-carrier implication is a normalized
routed source clause. -/
theorem carrierMetadataNormalizedClauses_disjoint_routedClause
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    List.Disjoint
      (carrierMetadataNormalizedClauses source)
      (routedClauseMetadataNormalizedClauses source) := by
  rw [List.disjoint_left]
  intro clause carrierClauseMember routedClauseMember
  rw [carrierMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq] at carrierClauseMember
  rcases List.mem_map.mp carrierClauseMember with
    ⟨carrierTaggedLink, carrierTaggedMember, carrierClauseEq⟩
  rcases carrierTaggedLink with ⟨normalizedLink, direction⟩
  rcases List.mem_product.mp carrierTaggedMember with
    ⟨normalizedLinkMember, _directionMember⟩
  rcases List.mem_map.mp normalizedLinkMember with
    ⟨carrierLink, carrierLinkMember, normalizedLinkEq⟩
  subst normalizedLink
  rw [routedClauseMetadataNormalizedClauses_eq_sites]
    at routedClauseMember
  rcases List.mem_flatMap.mp routedClauseMember with
    ⟨taggedClause, _taggedClauseMember, translatedMember⟩
  rcases List.mem_map.mp translatedMember with
    ⟨translate, _translateMember, routedClauseEq⟩
  let normalizedCarrierLink :=
    PeriodicEquality.normalizeLink
      (carrierWrappedVariableNormalization source) carrierLink
  let firstLiteral : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable Variable) :=
    ⟨normalizedCarrierLink.first, (0, 0), direction⟩
  let secondLiteral : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable Variable) :=
    ⟨normalizedCarrierLink.second,
      normalizedCarrierLink.relativeOffset, !direction⟩
  have firstLiteralMember : firstLiteral ∈
      PeriodicEquality.normalizedClause
        (normalizedCarrierLink, direction) := by
    cases direction <;>
      simp [firstLiteral, PeriodicEquality.normalizedClause]
  have secondLiteralMember : secondLiteral ∈
      PeriodicEquality.normalizedClause
        (normalizedCarrierLink, direction) := by
    cases direction <;>
      simp [secondLiteral, PeriodicEquality.normalizedClause]
  have normalizedClauseEq :
      PeriodicEquality.normalizedClause
          (normalizedCarrierLink, direction) =
        normalizedRoutedClauseAt source
          (taggedClause.2, translate) :=
    carrierClauseEq.trans routedClauseEq.symm
  have routedFirstLiteralMember : firstLiteral ∈
      normalizedRoutedClauseAt source
        (taggedClause.2, translate) := by
    rw [← normalizedClauseEq]
    exact firstLiteralMember
  have routedSecondLiteralMember : secondLiteral ∈
      normalizedRoutedClauseAt source
        (taggedClause.2, translate) := by
    rw [← normalizedClauseEq]
    exact secondLiteralMember
  rcases normalizedRoutedClauseAt_literal_original_eq_terminal_start
      source (taggedClause.2, translate) routedFirstLiteralMember with
    ⟨firstIndexed, firstOriginalEq⟩
  rcases normalizedRoutedClauseAt_literal_original_eq_terminal_start
      source (taggedClause.2, translate) routedSecondLiteralMember with
    ⟨secondIndexed, secondOriginalEq⟩
  have normalizedFirstEq :
      normalizedCarrierLink.first.original =
        PeriodicPlanarSATVariable.terminal firstIndexed .start := by
    simpa [firstLiteral] using firstOriginalEq
  have normalizedSecondEq :
      normalizedCarrierLink.second.original =
        PeriodicPlanarSATVariable.terminal secondIndexed .start := by
    simpa [secondLiteral] using secondOriginalEq
  rcases retainedCarrierLink_first_eq_terminal_start_of_normalized
      source carrierLink normalizedFirstEq with
    ⟨firstTerminal, firstNodeEq, firstEndpointEq⟩
  rcases retainedCarrierLink_second_eq_terminal_start_of_normalized
      source carrierLink normalizedSecondEq with
    ⟨secondTerminal, secondNodeEq, secondEndpointEq⟩
  have firstTerminalMember : firstTerminal ∈
      drawingSegmentTerminals source.incidenceGraph :=
    retainedDrawingCompleteCarrierLink_terminal_mem
      source.incidenceGraph carrierLinkMember (Or.inl firstNodeEq)
  have secondTerminalMember : secondTerminal ∈
      drawingSegmentTerminals source.incidenceGraph :=
    retainedDrawingCompleteCarrierLink_terminal_mem
      source.incidenceGraph carrierLinkMember (Or.inr secondNodeEq)
  have carrierKeyEq : firstTerminal.carrierKey =
      secondTerminal.carrierKey := by
    have common := retainedDrawingCompleteCarrierLinks_common_key
      source.incidenceGraph carrierLinkMember
    simpa [firstNodeEq, secondNodeEq, CarrierNode.carrierKey] using common
  have terminalData :=
    segmentTerminals_indexed_translate_eq_of_carrierKey_eq
      source.incidenceGraph firstTerminalMember secondTerminalMember
      carrierKeyEq
  have terminalEq : firstTerminal = secondTerminal :=
    SegmentTerminal.eq_of_fields_eq terminalData.1 terminalData.2
      (firstEndpointEq.trans secondEndpointEq.symm)
  apply retainedDrawingCompleteCarrierLink_endpoints_ne
    wellFormed degree isLocal carrierLinkMember
  rw [firstNodeEq, secondNodeEq, terminalEq]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
