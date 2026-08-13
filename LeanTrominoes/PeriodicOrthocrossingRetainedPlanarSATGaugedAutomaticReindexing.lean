/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedReindexedRepresentatives
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceClauseTranslation

/-!
# Automatic reindexing of translated final segment sources

The generic reindexing construction only needs one orbit-specific premise:
the physically translated source still belongs to the retained finite
component family.  Clause-shape invariance supplies the translated clause and
literal automatically, while retained-source exhaustiveness supplies its
global metadata index.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Choose the unique flat finite-drawing index of a metadata-rich physical
incidence. -/
private theorem exists_metadataPhysicalIncidenceIndex
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataIndex : Nat)
    (literal : PlanarSATVariable Variable × Bool)
    (literalIndex : Nat)
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata formula)[
          metadataIndex]? = some metadata)
    (literalMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx) :
    ∃ physicalIncidenceIndex : Nat,
      (metadataPhysicalIncidence
          metadata metadataIndex literal literalIndex,
        physicalIncidenceIndex) ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).incidences.zipIdx := by
  have incidenceMember :=
    metadataPhysicalIncidence_mem
      formula metadata metadataIndex literal literalIndex
      metadataLookup literalMember
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨physicalIncidenceIndex, indexLt, lookup⟩
  refine ⟨physicalIncidenceIndex, ?_⟩
  rw [List.mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff]
  exact ⟨indexLt, lookup⟩

/-- Retained membership of a translated source automatically produces all
metadata, clause, and literal fields needed to reindex a final segment
occurrence. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.exists_metadataReindexing_of_sourceMember
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift reindexShift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (translatedSourceMember :
      (witness.routeWitness.metadata.source.periodTranslate
        formula reindexShift).RetainedComponentMember formula) :
    Nonempty
      (FinalGaugedSegmentMetadataReindexing
        witness reindexShift) := by
  let sourceMetadata := witness.routeWitness.metadata
  have sourceMetadataMember :
      sourceMetadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨witness.routeWitness.metadataIndex,
        witness.routeWitness.metadataLookup⟩
  have sourceValid : sourceMetadata.RetainedValid formula :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula sourceMetadataMember
  have sourceLocalClauseMember :
      (sourceMetadata.clause,
          sourceMetadata.source.localClauseIndex) ∈
        (sourceMetadata.source.clauseFormula formula).zipIdx :=
    (sourceMetadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).1 sourceValid |>.2
  rcases
      sourceMetadata.source.exists_periodTranslatedClauseLiteral
        formula reindexShift
        sourceMetadata.clause sourceLocalClauseMember
        witness.routeWitness.literal witness.taggedLiteral.2
        witness.routeWitness.literalMember with
    ⟨targetClause, targetLiteral,
      targetLocalClauseMember, targetLiteralMember⟩
  let targetSource :=
    sourceMetadata.source.periodTranslate formula reindexShift
  rcases exists_retainedMetadataLookup_of_sourceMember
      formula targetSource targetClause translatedSourceMember
      targetLocalClauseMember with
    ⟨targetMetadataIndex, targetMetadataLookup⟩
  rcases exists_metadataPhysicalIncidenceIndex
      formula ⟨targetClause, targetSource⟩
      targetMetadataIndex targetLiteral witness.taggedLiteral.2
      targetMetadataLookup targetLiteralMember with
    ⟨targetPhysicalIncidenceIndex,
      targetPhysicalIncidenceMember⟩
  exact ⟨{
    targetMetadata := ⟨targetClause, targetSource⟩
    targetMetadataIndex := targetMetadataIndex
    targetMetadataLookup := targetMetadataLookup
    targetLiteral := targetLiteral
    targetLiteralMember := targetLiteralMember
    targetPhysicalIncidenceIndex :=
      targetPhysicalIncidenceIndex
    targetPhysicalIncidenceMember :=
      targetPhysicalIncidenceMember
    targetComponentEq := rfl
    targetLocalClauseIndexEq :=
      DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate
        formula sourceMetadata.source reindexShift
  }⟩

/-- Retained membership of a translated source therefore gives a finite
representative at the adjusted common physical shift. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.exists_commonShiftRepresentative_of_sourceMember
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift reindexShift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (translatedSourceMember :
      (witness.routeWitness.metadata.source.periodTranslate
        formula reindexShift).RetainedComponentMember formula) :
    Nonempty
      (FinalGaugedSegmentCommonShiftRepresentative
        formula indexed shift
          (Cell.sub witness.physicalShift reindexShift)) := by
  rcases witness.exists_metadataReindexing_of_sourceMember
      translatedSourceMember with
    ⟨reindexing⟩
  exact reindexing.exists_commonShiftRepresentative

/-- A retained target source may differ in enumeration-only fields from the
literal period translate, as long as it selects the same translated component
and local clause index.  This flexibility is needed for routed-variable arms,
whose global per-site index can change near the edge of the retained window. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.exists_metadataReindexing_of_targetSource
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift reindexShift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (targetSource : DrawingPlanarSATClauseSource Variable)
    (targetSourceMember :
      targetSource.RetainedComponentMember formula)
    (targetComponentEq :
      targetSource.component =
        (witness.routeWitness.metadata.source.periodTranslate
          formula reindexShift).component)
    (targetLocalClauseIndexEq :
      targetSource.localClauseIndex =
        witness.routeWitness.metadata.source.localClauseIndex) :
    Nonempty
      (FinalGaugedSegmentMetadataReindexing
        witness reindexShift) := by
  let sourceMetadata := witness.routeWitness.metadata
  have sourceMetadataMember :
      sourceMetadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨witness.routeWitness.metadataIndex,
        witness.routeWitness.metadataLookup⟩
  have sourceValid : sourceMetadata.RetainedValid formula :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula sourceMetadataMember
  have sourceLocalClauseMember :
      (sourceMetadata.clause,
          sourceMetadata.source.localClauseIndex) ∈
        (sourceMetadata.source.clauseFormula formula).zipIdx :=
    (sourceMetadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).1 sourceValid |>.2
  rcases
      sourceMetadata.source.exists_periodTranslatedClauseLiteral
        formula reindexShift
        sourceMetadata.clause sourceLocalClauseMember
        witness.routeWitness.literal witness.taggedLiteral.2
        witness.routeWitness.literalMember with
    ⟨targetClause, targetLiteral,
      translatedLocalClauseMember, targetLiteralMember⟩
  let translatedSource :=
    sourceMetadata.source.periodTranslate formula reindexShift
  have targetFormulaEq :
      targetSource.clauseFormula formula =
        translatedSource.clauseFormula formula :=
    targetSource.clauseFormula_eq_of_component_eq
      formula translatedSource targetComponentEq
  have translatedLocalIndexEq :
      translatedSource.localClauseIndex =
        sourceMetadata.source.localClauseIndex :=
    DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate
      formula sourceMetadata.source reindexShift
  have targetLocalClauseMember :
      (targetClause, targetSource.localClauseIndex) ∈
        (targetSource.clauseFormula formula).zipIdx := by
    rw [targetFormulaEq, targetLocalClauseIndexEq,
      ← translatedLocalIndexEq]
    exact translatedLocalClauseMember
  rcases exists_retainedMetadataLookup_of_sourceMember
      formula targetSource targetClause targetSourceMember
      targetLocalClauseMember with
    ⟨targetMetadataIndex, targetMetadataLookup⟩
  rcases exists_metadataPhysicalIncidenceIndex
      formula ⟨targetClause, targetSource⟩
      targetMetadataIndex targetLiteral witness.taggedLiteral.2
      targetMetadataLookup targetLiteralMember with
    ⟨targetPhysicalIncidenceIndex,
      targetPhysicalIncidenceMember⟩
  exact ⟨{
    targetMetadata := ⟨targetClause, targetSource⟩
    targetMetadataIndex := targetMetadataIndex
    targetMetadataLookup := targetMetadataLookup
    targetLiteral := targetLiteral
    targetLiteralMember := targetLiteralMember
    targetPhysicalIncidenceIndex :=
      targetPhysicalIncidenceIndex
    targetPhysicalIncidenceMember :=
      targetPhysicalIncidenceMember
    targetComponentEq := targetComponentEq
    targetLocalClauseIndexEq := targetLocalClauseIndexEq
  }⟩

/-- Component-equivalent retained target sources therefore produce finite
representatives at the same adjusted common physical shift as literal source
translation. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.exists_commonShiftRepresentative_of_targetSource
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift reindexShift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (targetSource : DrawingPlanarSATClauseSource Variable)
    (targetSourceMember :
      targetSource.RetainedComponentMember formula)
    (targetComponentEq :
      targetSource.component =
        (witness.routeWitness.metadata.source.periodTranslate
          formula reindexShift).component)
    (targetLocalClauseIndexEq :
      targetSource.localClauseIndex =
        witness.routeWitness.metadata.source.localClauseIndex) :
    Nonempty
      (FinalGaugedSegmentCommonShiftRepresentative
        formula indexed shift
          (Cell.sub witness.physicalShift reindexShift)) := by
  rcases witness.exists_metadataReindexing_of_targetSource
      targetSource targetSourceMember targetComponentEq
      targetLocalClauseIndexEq with
    ⟨reindexing⟩
  exact reindexing.exists_commonShiftRepresentative

/-- Reindexing through a physically translated source preserves the
anchor-normalized canonically gauged clause.  This is the clause-orbit
identity later used to show that reindexing cannot collapse two distinct
final segment occurrences. -/
theorem
    FinalGaugedSegmentMetadataReindexing.target_normalizedClause_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift reindexShift : Cell}
    {witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift}
    (reindexing :
      FinalGaugedSegmentMetadataReindexing
        witness reindexShift) :
    metadataGaugedNormalizedClause
        formula reindexing.targetMetadata =
      metadataGaugedNormalizedClause
        formula witness.routeWitness.metadata := by
  let sourceMetadata := witness.routeWitness.metadata
  let translatedSource :=
    sourceMetadata.source.periodTranslate formula reindexShift
  have sourceMetadataMember :
      sourceMetadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨witness.routeWitness.metadataIndex,
        witness.routeWitness.metadataLookup⟩
  have sourceValid : sourceMetadata.RetainedValid formula :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula sourceMetadataMember
  have sourceLocalClauseMember :
      (sourceMetadata.clause,
          sourceMetadata.source.localClauseIndex) ∈
        (sourceMetadata.source.clauseFormula formula).zipIdx :=
    (sourceMetadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp sourceValid |>.2
  have targetMetadataMember :
      reindexing.targetMetadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨reindexing.targetMetadataIndex,
        reindexing.targetMetadataLookup⟩
  have targetValid :
      reindexing.targetMetadata.RetainedValid formula :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula targetMetadataMember
  have targetLocalClauseMember :
      (reindexing.targetMetadata.clause,
          reindexing.targetMetadata.source.localClauseIndex) ∈
        (reindexing.targetMetadata.source.clauseFormula
          formula).zipIdx :=
    (reindexing.targetMetadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp targetValid |>.2
  have targetFormulaEq :
      reindexing.targetMetadata.source.clauseFormula formula =
        translatedSource.clauseFormula formula :=
    reindexing.targetMetadata.source.clauseFormula_eq_of_component_eq
      formula translatedSource reindexing.targetComponentEq
  have translatedTargetMember :
      (reindexing.targetMetadata.clause,
          translatedSource.localClauseIndex) ∈
        (translatedSource.clauseFormula formula).zipIdx := by
    rw [← targetFormulaEq]
    have translatedIndexEq :
        translatedSource.localClauseIndex =
          reindexing.targetMetadata.source.localClauseIndex := by
      change
        (sourceMetadata.source.periodTranslate
            formula reindexShift).localClauseIndex =
          reindexing.targetMetadata.source.localClauseIndex
      rw [DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate,
        ← reindexing.targetLocalClauseIndexEq]
    rw [translatedIndexEq]
    exact targetLocalClauseMember
  simpa only [metadataGaugedNormalizedClause,
      gaugedPeriodicPlanarSATClause, sourceMetadata,
      translatedSource] using
    sourceMetadata.source
      |>.anchorNormalizedGaugedClause_periodTranslate
        formula reindexShift sourceMetadata.clause
        reindexing.targetMetadata.clause
        sourceLocalClauseMember translatedTargetMember

/-- The target metadata clause anchor is the source metadata clause anchor
plus the physical source-reindexing shift. -/
theorem
    FinalGaugedSegmentMetadataReindexing.target_clauseAnchor_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift reindexShift : Cell}
    {witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift}
    (reindexing :
      FinalGaugedSegmentMetadataReindexing
        witness reindexShift)
    (sourceClauseNonempty :
      witness.routeWitness.metadata.clause.literals ≠ []) :
    PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause
          formula reindexing.targetMetadata).literals =
      Cell.add
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula witness.routeWitness.metadata).literals)
        reindexShift := by
  let sourceMetadata := witness.routeWitness.metadata
  let translatedSource :=
    sourceMetadata.source.periodTranslate formula reindexShift
  have sourceMetadataMember :
      sourceMetadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨witness.routeWitness.metadataIndex,
        witness.routeWitness.metadataLookup⟩
  have sourceValid : sourceMetadata.RetainedValid formula :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula sourceMetadataMember
  have sourceLocalClauseMember :
      (sourceMetadata.clause,
          sourceMetadata.source.localClauseIndex) ∈
        (sourceMetadata.source.clauseFormula formula).zipIdx :=
    (sourceMetadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp sourceValid |>.2
  have targetMetadataMember :
      reindexing.targetMetadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨reindexing.targetMetadataIndex,
        reindexing.targetMetadataLookup⟩
  have targetValid :
      reindexing.targetMetadata.RetainedValid formula :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula targetMetadataMember
  have targetLocalClauseMember :
      (reindexing.targetMetadata.clause,
          reindexing.targetMetadata.source.localClauseIndex) ∈
        (reindexing.targetMetadata.source.clauseFormula
          formula).zipIdx :=
    (reindexing.targetMetadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp targetValid |>.2
  have targetFormulaEq :
      reindexing.targetMetadata.source.clauseFormula formula =
        translatedSource.clauseFormula formula :=
    reindexing.targetMetadata.source.clauseFormula_eq_of_component_eq
      formula translatedSource reindexing.targetComponentEq
  have translatedTargetMember :
      (reindexing.targetMetadata.clause,
          translatedSource.localClauseIndex) ∈
        (translatedSource.clauseFormula formula).zipIdx := by
    rw [← targetFormulaEq]
    have translatedIndexEq :
        translatedSource.localClauseIndex =
          reindexing.targetMetadata.source.localClauseIndex := by
      change
        (sourceMetadata.source.periodTranslate
            formula reindexShift).localClauseIndex =
          reindexing.targetMetadata.source.localClauseIndex
      rw [DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate,
        ← reindexing.targetLocalClauseIndexEq]
    rw [translatedIndexEq]
    exact targetLocalClauseMember
  simpa only [metadataGaugedPositionedClause,
      gaugedPeriodicPlanarSATClause, sourceMetadata,
      translatedSource] using
    sourceMetadata.source.clauseAnchor_periodTranslate
      formula reindexShift sourceMetadata.clause
      reindexing.targetMetadata.clause
      sourceLocalClauseMember translatedTargetMember
      (by simpa only [sourceMetadata] using sourceClauseNonempty)

end PeriodicOrthocrossing
end LeanTrominoes
