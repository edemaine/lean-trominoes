/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixProfileCoordinateBlocks
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceTailData

/-! # Figure 9 occurrences with their complete source provenance

The proof-side stream keeps the parent clause, generated-clause offset,
directed profile, and tail table together with each header. Its pair
projection is the existing machine input, so adding provenance does not
change serialization or the verified machines.
-/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeFigureNineSourceTail
open PlanarOneInThreeNoUnitsFigureNine

/-- One output occurrence together with the source data that selected both
its finite header and dynamic tail. -/
structure SourceOccurrence where
  parentClauseIndex : Nat
  generatedClauseStart : Nat
  profile : DirectedClauseProfile
  orderedTails : List (List AxisDirection)
  header : Header

/-- Erase provenance to recover the exact header/tail machine input. -/
def SourceOccurrence.pair (occurrence : SourceOccurrence) :
    Header × List AxisDirection :=
  (occurrence.header,
    selectedTailDirections occurrence.orderedTails occurrence.header)

/-- Original source block and local generated-clause key, as used by
`ClauseMetadata.key`. -/
def SourceOccurrence.metadataKey (occurrence : SourceOccurrence) : Nat × Nat :=
  (occurrence.parentClauseIndex,
    (headerTemplateCoordinate occurrence.header).clauseIndex)

/-- Absolute generated clause selected by this occurrence. -/
def SourceOccurrence.generatedClauseIndex (occurrence : SourceOccurrence) : Nat :=
  occurrence.generatedClauseStart + occurrence.metadataKey.2

/-- Source literal selected before applying the polarity operation. -/
def SourceOccurrence.sourceIndex (occurrence : SourceOccurrence) : Nat × Nat :=
  (occurrence.generatedClauseIndex,
    occurrence.header.polarity.indexed.sourceLiteralIndex)

/-- Number of generated clauses in one original source block. -/
def generatedClauseCount (profile : DirectedClauseProfile) : Nat :=
  (templateDrawingOfClauseProfile
    (clauseProfile (orderedDirectedProfile profile))).formula.length

/-- Enumerate both indices in the same traversal that attaches each
header's tail. Variable markers consume neither index nor a tail row. -/
def sourceOccurrencesFrom (parentClauseIndex generatedClauseStart : Nat) :
    List FormulaShapeDirectionOrdering.Token →
      List (List (List AxisDirection)) → List SourceOccurrence
  | [], _ => []
  | .variable :: source, tailTables =>
      sourceOccurrencesFrom parentClauseIndex generatedClauseStart
        source tailTables
  | .clause profile :: source, tailTables =>
      ((sourceClauseHeaders profile).map fun header =>
        { parentClauseIndex, generatedClauseStart, profile,
          orderedTails := tailTables.headD [], header }) ++
      sourceOccurrencesFrom (parentClauseIndex + 1)
        (generatedClauseStart + generatedClauseCount profile)
        source tailTables.tail

/-- The complete occurrence stream starts both indices at zero. -/
def sourceOccurrences := sourceOccurrencesFrom 0 0

/-- Erasing provenance preserves every pair and its absolute list position,
including malformed tail-table fallbacks. -/
@[simp] theorem sourceOccurrencesFrom_map_pair
    (parentClauseIndex generatedClauseStart : Nat)
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    (sourceOccurrencesFrom parentClauseIndex generatedClauseStart
      source tailTables).map SourceOccurrence.pair =
      sourcePairs source tailTables := by
  induction source generalizing parentClauseIndex generatedClauseStart tailTables with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» => exact induction _ _ _
      | clause profile =>
          simp only [sourceOccurrencesFrom, sourcePairs, List.map_append,
            List.map_map, induction, sourceClausePairs]
          rfl

@[simp] theorem sourceOccurrences_map_pair
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    (sourceOccurrences source tailTables).map SourceOccurrence.pair =
      sourcePairs source tailTables :=
  sourceOccurrencesFrom_map_pair 0 0 source tailTables

private theorem sourceClauseHeaders_map_clauseIndex :
    ∀ profile : DirectedClauseProfile,
      (sourceClauseHeaders profile).map
          (fun header => (headerTemplateCoordinate header).clauseIndex) =
        (expectedSourceClauseHeaderTemplateProfileCoordinateBlocks
          profile).zipIdx.flatMap fun taggedBlock =>
            List.replicate taggedBlock.1.length taggedBlock.2 := by
  native_decide

private theorem sourceClauseHeaders_map_shiftedClauseIndex
    (profile : DirectedClauseProfile) (start : Nat) :
    (sourceClauseHeaders profile).map
        (fun header => start + (headerTemplateCoordinate header).clauseIndex) =
      ((expectedSourceClauseHeaderTemplateProfileCoordinateBlocks
        profile).zipIdx start).flatMap fun taggedBlock =>
          List.replicate taggedBlock.1.length taggedBlock.2 := by
  have mapped := congrArg (List.map (start + ·))
    (sourceClauseHeaders_map_clauseIndex profile)
  rw [List.zipIdx_eq_map_add]
  simpa only [List.map_map, List.map_flatMap, List.map_replicate,
    List.flatMap_map, Function.comp_def] using mapped

/-- The generated-clause column is obtained from the same records as the
header/tail column. Empty blocks still advance the clause index. -/
theorem sourceOccurrencesFrom_map_generatedClauseIndex
    (parentClauseIndex generatedClauseStart : Nat)
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    (sourceOccurrencesFrom parentClauseIndex generatedClauseStart
      source tailTables).map SourceOccurrence.generatedClauseIndex =
      ((source.flatMap expectedHeaderTemplateProfileCoordinateBlocks).zipIdx
        generatedClauseStart).flatMap fun taggedBlock =>
          List.replicate taggedBlock.1.length taggedBlock.2 := by
  induction source generalizing parentClauseIndex generatedClauseStart tailTables with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa only [sourceOccurrencesFrom, List.flatMap_cons,
            expectedHeaderTemplateProfileCoordinateBlocks, List.nil_append]
            using induction parentClauseIndex generatedClauseStart tailTables
      | clause profile =>
          simp only [sourceOccurrencesFrom, List.map_append, List.map_map,
            SourceOccurrence.generatedClauseIndex, SourceOccurrence.metadataKey,
            Function.comp_def, List.flatMap_cons,
            expectedHeaderTemplateProfileCoordinateBlocks, List.zipIdx_append,
            List.flatMap_append]
          rw [sourceClauseHeaders_map_shiftedClauseIndex, induction]
          simp only [expectedSourceClauseHeaderTemplateProfileCoordinateBlocks,
            List.length_map, List.length_zipIdx, generatedClauseCount]

theorem sourceOccurrences_map_generatedClauseIndex
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    (sourceOccurrences source tailTables).map
        SourceOccurrence.generatedClauseIndex =
      (source.flatMap expectedHeaderTemplateProfileCoordinateBlocks).zipIdx.flatMap
        fun taggedBlock => List.replicate taggedBlock.1.length taggedBlock.2 :=
  sourceOccurrencesFrom_map_generatedClauseIndex 0 0 source tailTables

private theorem sourceOccurrencesFrom_variables
    (parentClauseIndex generatedClauseStart count : Nat) :
    sourceOccurrencesFrom parentClauseIndex generatedClauseStart
      (List.replicate count Token.variable) [] = [] := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simpa [List.replicate_succ, sourceOccurrencesFrom] using induction

/-- All fields of an occurrence come from the same indexed source clause.
The parent index is retained even when different clauses have equal profiles
or equal-valued headers. -/
private theorem sourceOccurrencesFrom_provenance
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauses : List (PositionedPeriodicClause Variable))
    (parentStart generatedStart variableCount : Nat)
    (occurrence : SourceOccurrence)
    (member : occurrence ∈
      sourceOccurrencesFrom parentStart generatedStart
        (((clauses.zipIdx parentStart).map fun taggedClause =>
          Token.clause (DirectedClauseProfile.ofClause
            routes taggedClause.2 taggedClause.1)) ++
          List.replicate variableCount Token.variable)
        ((clauses.zipIdx parentStart).map fun taggedClause =>
          orderedTailDirections routes taggedClause.2 taggedClause.1)) :
    ∃ clause,
      (clause, occurrence.parentClauseIndex) ∈ clauses.zipIdx parentStart ∧
      occurrence.profile = DirectedClauseProfile.ofClause
        routes occurrence.parentClauseIndex clause ∧
      occurrence.orderedTails = orderedTailDirections
        routes occurrence.parentClauseIndex clause ∧
      occurrence.header ∈ sourceClauseHeaders occurrence.profile := by
  induction clauses generalizing parentStart generatedStart with
  | nil =>
      simp only [List.zipIdx_nil, List.map_nil, List.nil_append] at member
      rw [sourceOccurrencesFrom_variables] at member
      exact False.elim (List.not_mem_nil member)
  | cons clause clauses induction =>
      simp only [List.zipIdx_cons, List.map_cons, List.cons_append,
        sourceOccurrencesFrom, List.headD_cons, List.tail_cons,
        List.mem_append] at member
      rcases member with headMember | tailMember
      · rcases List.mem_map.mp headMember with ⟨header, headerMember, equality⟩
        subst occurrence
        exact ⟨clause, by simp [List.zipIdx_cons], rfl, rfl, headerMember⟩
      · rcases induction (parentStart + 1) _ tailMember with
          ⟨sourceClause, sourceMember, profileEq, tailsEq, headerMember⟩
        exact ⟨sourceClause,
          by simpa only [List.zipIdx_cons] using
            List.mem_cons_of_mem (clause, parentStart) sourceMember,
          profileEq, tailsEq, headerMember⟩

/-- One provenance witness for each occurrence in a positioned formula. -/
theorem sourceOccurrences_ofFormula_provenance
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (occurrence : SourceOccurrence)
    (member : occurrence ∈
      sourceOccurrences (FormulaShapeDirectionOrdering.ofFormula source routes)
        (source.clauses.zipIdx.map fun taggedClause =>
          orderedTailDirections routes taggedClause.2 taggedClause.1)) :
    ∃ clause,
      source.clauses[occurrence.parentClauseIndex]? = some clause ∧
      occurrence.profile = DirectedClauseProfile.ofClause
        routes occurrence.parentClauseIndex clause ∧
      occurrence.orderedTails = orderedTailDirections
        routes occurrence.parentClauseIndex clause ∧
      occurrence.header ∈ sourceClauseHeaders occurrence.profile := by
  obtain ⟨clause, clauseMember, profileEq, tailsEq, headerMember⟩ :=
    sourceOccurrencesFrom_provenance routes source.clauses 0 0
      source.erase.variableOccurrences.dedup.length occurrence
      (by simpa only [sourceOccurrences, FormulaShapeDirectionOrdering.ofFormula]
        using member)
  exact ⟨clause, List.mk_mem_zipIdx_iff_getElem?.mp clauseMember,
    profileEq, tailsEq, headerMember⟩

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
