/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterSemanticEntries

/-! # Enumeration identities for source-occurrence semantic entries -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

/-- The recursive clause-entry view is the ordinary indexed metadata block. -/
theorem clauseEntriesFrom_eq_zipIdx (clause : PeriodicClause Nat)
    (clauseIndex literalIndex edgeIndex : Nat)
    (literals : List (PeriodicLiteral Nat)) :
    clauseEntriesFrom clause clauseIndex literalIndex edgeIndex literals =
      ((literals.zipIdx literalIndex).map fun taggedLiteral =>
        (CNFIncidence.mk clauseIndex clause taggedLiteral.2
          taggedLiteral.1)).zipIdx edgeIndex := by
  induction literals generalizing literalIndex edgeIndex with
  | nil => rfl
  | cons literal literals induction =>
      simp only [clauseEntriesFrom, List.zipIdx_cons, List.map_cons,
        induction]

/-- A whole recursive clause block is its indexed incidence-metadata block. -/
theorem clauseEntriesFrom_self_eq_metadata (clause : PeriodicClause Nat)
    (clauseIndex edgeIndex : Nat) :
    clauseEntriesFrom clause clauseIndex 0 edgeIndex clause =
      (PeriodicCNF.incidenceMetadataBlock
        (clause, clauseIndex)).zipIdx edgeIndex := by
  rw [clauseEntriesFrom_eq_zipIdx]
  rfl

/-- The recursive formula-entry view is the indexed flattened incidence
metadata stream starting at the supplied indices. -/
theorem formulaEntriesFrom_eq_zipIdx (clauses : List (PeriodicClause Nat))
    (clauseIndex edgeIndex : Nat) :
    formulaEntriesFrom clauses clauseIndex edgeIndex =
      (PeriodicCNF.incidenceMetadataBlocksFrom
        clauseIndex clauses).zipIdx edgeIndex := by
  induction clauses generalizing clauseIndex edgeIndex with
  | nil => rfl
  | cons clause clauses induction =>
      rw [formulaEntriesFrom, clauseEntriesFrom_self_eq_metadata,
        induction]
      unfold PeriodicCNF.incidenceMetadataBlocksFrom
      simp only [List.zipIdx_cons, List.flatMap_cons,
        List.zipIdx_append]
      simp

/-- At zero, formula entries are exactly the globally indexed source
incidences used by occurrence-route descriptors. -/
theorem formulaEntriesFrom_zero (source : PeriodicCNF Nat) :
    formulaEntriesFrom source.clauses 0 0 =
      (PeriodicCNF.incidencesWithMetadata source).zipIdx := by
  rw [formulaEntriesFrom_eq_zipIdx,
    PeriodicCNF.incidenceMetadataBlocksFrom_zero]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
