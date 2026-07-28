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
  exact ⟨{
    targetMetadata := ⟨targetClause, targetSource⟩
    targetMetadataIndex := targetMetadataIndex
    targetMetadataLookup := targetMetadataLookup
    targetLiteral := targetLiteral
    targetLiteralMember := targetLiteralMember
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
  exact ⟨{
    targetMetadata := ⟨targetClause, targetSource⟩
    targetMetadataIndex := targetMetadataIndex
    targetMetadataLookup := targetMetadataLookup
    targetLiteral := targetLiteral
    targetLiteralMember := targetLiteralMember
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

end PeriodicOrthocrossing
end LeanTrominoes
