/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipIdxFstMembership
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseNormalizedFamilyDeduplication
import LeanTrominoes.PeriodicCNFPlanarIncidences

/-! # Duplicate-freedom of base normalized routed clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- At zero translation, the wrapped normalized routed clause is the exact
zero-offset terminal-literal block of its incidence occurrences. -/
theorem normalizedRoutedClauseAt_base_eq_occurrences
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (clauseIndex : Nat) :
    normalizedRoutedClauseAt source (clauseIndex, (0, 0)) =
      (clauseRouteOccurrencesAt
        source (clauseIndex, (0, 0))).map fun occurrence =>
          (⟨⟨PeriodicPlanarSATVariable.terminal
              (occurrence.sourceTerminal source).indexed .start⟩,
            (0, 0), occurrence.incidence.literal.value⟩ :
            PeriodicLiteral
              (WrappedPeriodicPlanarSATVariable Variable)) := by
  unfold normalizedRoutedClauseAt
  rw [periodicizeRoutedClauseAt_external_eq_commonOffset
    source wellFormed (clauseIndex, (0, 0))]
  cases occurrencesEq :
      clauseRouteOccurrencesAt source (clauseIndex, (0, 0)) with
  | nil => rfl
  | cons first rest =>
      simp [PeriodicClause.anchorNormalize,
        PeriodicCNF.clauseAnchor,
        PeriodicLiteral.anchorNormalize,
        Cell.sub]

/-- Every nonempty indexed source clause contributes at least one base
route occurrence. -/
theorem exists_baseClauseRouteOccurrence
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedClauseMember : taggedClause ∈ source.clauses.zipIdx)
    (clauseNonempty : taggedClause.1 ≠ []) :
    ∃ occurrence,
      occurrence ∈ clauseRouteOccurrencesAt
        source (taggedClause.2, (0, 0)) := by
  cases clauseEq : taggedClause.1 with
  | nil => exact (clauseNonempty clauseEq).elim
  | cons literal literals =>
      let incidence : CNFIncidence Variable :=
        ⟨taggedClause.2, taggedClause.1, 0, literal⟩
      have taggedLiteralMember :
          (literal, 0) ∈ taggedClause.1.zipIdx := by
        rw [clauseEq]
        simp
      have incidenceMember :
          incidence ∈ incidencesWithMetadata source := by
        apply (mem_incidencesWithMetadata_iff source incidence).mpr
        exact ⟨taggedClauseMember, taggedLiteralMember⟩
      rcases exists_mem_zipIdx_fst
        (incidencesWithMetadata source) 0 incidenceMember with
          ⟨edgeIndex, taggedIncidenceMember⟩
      let occurrence : CNFRouteOccurrence Variable :=
        ⟨incidence, edgeIndex, (0, 0)⟩
      refine ⟨occurrence, ?_⟩
      unfold clauseRouteOccurrencesAt
      apply List.mem_map.mpr
      refine ⟨(incidence, edgeIndex), ?_, rfl⟩
      apply List.mem_filter.mpr
      exact ⟨taggedIncidenceMember, by simp [incidence]⟩

/-- If all source clauses are nonempty, distinct clause indices yield
distinct base normalized routed clauses. -/
theorem baseRoutedClauseNormalizedClauses_nodup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (clausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (baseRoutedClauseNormalizedClauses source).Nodup := by
  unfold baseRoutedClauseNormalizedClauses
  have taggedClausesNodup : source.clauses.zipIdx.Nodup :=
    (List.nodup_zipIdx_map_snd source.clauses).of_map Prod.snd
  apply taggedClausesNodup.map_on
  intro first firstMember second secondMember clauseEq
  have firstNonempty := clausesNonempty first.1
    (List.fst_mem_of_mem_zipIdx firstMember)
  rcases exists_baseClauseRouteOccurrence
    source first firstMember firstNonempty with
      ⟨firstOccurrence, firstOccurrenceMember⟩
  have firstLiteralMember :
      (⟨⟨PeriodicPlanarSATVariable.terminal
          (firstOccurrence.sourceTerminal source).indexed .start⟩,
        (0, 0), firstOccurrence.incidence.literal.value⟩ :
        PeriodicLiteral
          (WrappedPeriodicPlanarSATVariable Variable)) ∈
      normalizedRoutedClauseAt source
        (first.2, (0, 0)) := by
    rw [normalizedRoutedClauseAt_base_eq_occurrences
      source wellFormed first.2]
    exact List.mem_map.mpr
      ⟨firstOccurrence, firstOccurrenceMember, rfl⟩
  rw [clauseEq,
    normalizedRoutedClauseAt_base_eq_occurrences
      source wellFormed second.2] at firstLiteralMember
  rcases List.mem_map.mp firstLiteralMember with
    ⟨secondOccurrence, secondOccurrenceMember, literalEq⟩
  have indexedEq :
      (firstOccurrence.sourceTerminal source).indexed =
        (secondOccurrence.sourceTerminal source).indexed := by
    have wrappedAtomEq := congrArg
      (fun literal => literal.atom.original) literalEq.symm
    exact (PeriodicPlanarSATVariable.terminal.inj wrappedAtomEq).1
  have edgeIndexEq :
      firstOccurrence.edgeIndex = secondOccurrence.edgeIndex :=
    congrArg IndexedGridSegment.routeIndex indexedEq
  unfold clauseRouteOccurrencesAt at firstOccurrenceMember secondOccurrenceMember
  rcases List.mem_map.mp firstOccurrenceMember with
    ⟨firstTaggedIncidence, firstTaggedSelected, firstOccurrenceEq⟩
  rcases List.mem_map.mp secondOccurrenceMember with
    ⟨secondTaggedIncidence, secondTaggedSelected, secondOccurrenceEq⟩
  have firstTaggedMember := (List.mem_filter.mp firstTaggedSelected).1
  have secondTaggedMember := (List.mem_filter.mp secondTaggedSelected).1
  have firstClauseIndexEq :
      firstTaggedIncidence.1.clauseIndex = first.2 :=
    of_decide_eq_true (List.mem_filter.mp firstTaggedSelected).2
  have secondClauseIndexEq :
      secondTaggedIncidence.1.clauseIndex = second.2 :=
    of_decide_eq_true (List.mem_filter.mp secondTaggedSelected).2
  have taggedIncidenceEq :
      firstTaggedIncidence = secondTaggedIncidence := by
    apply tagged_eq_of_mem_zipIdx_of_snd_eq
      firstTaggedMember secondTaggedMember
    exact
      (congrArg CNFRouteOccurrence.edgeIndex
        firstOccurrenceEq).trans
      (edgeIndexEq.trans
        (congrArg CNFRouteOccurrence.edgeIndex
          secondOccurrenceEq).symm)
  have clauseIndexEq : first.2 = second.2 :=
    firstClauseIndexEq.symm.trans
      ((congrArg
        (fun tagged : CNFIncidence Variable × Nat =>
          tagged.1.clauseIndex) taggedIncidenceEq).trans
        secondClauseIndexEq)
  exact tagged_eq_of_mem_zipIdx_of_snd_eq
    firstMember secondMember clauseIndexEq

/-- Under the nonempty-clause hypothesis, routed-clause metadata deduplicates
exactly to one base clause per source clause. -/
theorem routedClauseMetadataNormalizedClauses_dedup_eq_base
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (clausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (routedClauseMetadataNormalizedClauses source).dedup =
      baseRoutedClauseNormalizedClauses source := by
  rw [routedClauseMetadataNormalizedClauses_dedup_eq_base_dedup
    source wellFormed]
  exact List.dedup_eq_self.mpr
    (baseRoutedClauseNormalizedClauses_nodup
      source wellFormed clausesNonempty)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
