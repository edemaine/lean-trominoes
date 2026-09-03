/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineMetadataParentProfileCoordinates

/-! # Clause arities selected by composed Figure 9 metadata -/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PeriodicCNF
open PeriodicCNF.ClauseProfileOccurrenceSplit
open PeriodicCNF.FormulaShapeOfFormula
open PlanarThreeSAT

/-- A concrete composed clause and the finite-template clause selected by
its metadata have the same literal count. -/
theorem metadata_clause_length_eq_template
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceNonempty :
      ∀ clause ∈ source.clauses, clause.literals ≠ [])
    (sourceWidth : source.erase.WidthAtMost 3)
    {metadata : ClauseMetadata Variable}
    (metadataMember : metadata ∈ formulaClauseMetadata source) :
    ∃ templateClause,
      (templateDrawingOfClauseProfile
        (clauseProfile
          (literalProfiles metadata.sourceClause.literals))).formula[
            metadata.localClauseIndex]? = some templateClause ∧
      metadata.clause.literals.length = templateClause.literals.length := by
  have valid := formulaClauseMetadata_valid source metadataMember
  have sourceMember : metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx valid.1
  have sourceClauseNonempty : metadata.sourceClause.literals ≠ [] :=
    sourceNonempty metadata.sourceClause sourceMember
  have sourceClauseWidth : metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr ⟨metadata.sourceClause, sourceMember, rfl⟩
  have embeddedMember :=
    localClauseMember_embedded
      metadata.sourceClauseIndex metadata.figureNineClauseStart
      metadata.sourceClause valid.2
  have instantiatedMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
          metadata.localClauseIndex) ∈
        (instantiatedDrawing metadata.sourceClauseIndex
          metadata.figureNineClauseStart metadata.sourceClause).formula.zipIdx := by
    rw [instantiatedDrawing_formula _ _ _ sourceClauseWidth]
    exact embeddedMember
  have transformedMember := instantiatedMember
  rw [instantiatedDrawing_eq] at transformedMember
  have transformedLookup :=
    (List.mem_zipIdx_iff_getElem?).mp transformedMember
  simp only [EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename, List.getElem?_map] at transformedLookup
  rcases Option.map_eq_some_iff.mp transformedLookup with
    ⟨renamedClause, renamedLookup, transformedClauseEq⟩
  rcases Option.map_eq_some_iff.mp renamedLookup with
    ⟨templateClause, templateLookup, renamedClauseEq⟩
  have templateEq :=
    templateDrawingOfClauseProfile_clauseProfile_literalProfiles
      metadata.sourceClause sourceClauseNonempty sourceClauseWidth
  refine ⟨templateClause, ?_, ?_⟩
  · rw [templateEq]
    exact templateLookup
  · calc
      metadata.clause.literals.length =
          (PlanarOneInThreeNoUnits.embedPositionedClause
            metadata.clause).literals.length := by
        simp [PlanarOneInThreeNoUnits.embedPositionedClause]
      _ = (EmbeddedClause.translate
          (Cell.scale composedGadgetScale metadata.sourceClause.position)
          renamedClause).literals.length := by
        exact congrArg (fun clause => clause.literals.length)
          transformedClauseEq.symm
      _ = renamedClause.literals.length := by
        simp [EmbeddedClause.translate]
      _ = (EmbeddedClause.rename
          (instantiatedVariableMap metadata.sourceClauseIndex
            metadata.figureNineClauseStart metadata.sourceClause)
          templateClause).literals.length := by
        exact congrArg (fun clause => clause.literals.length)
          renamedClauseEq.symm
      _ = templateClause.literals.length := by
        simp [EmbeddedClause.rename, EmbeddedClause.map]

/-- The total finite-template literal count stored by a metadata entry's
parent coordinate is the concrete composed clause's arity. -/
theorem metadata_clause_length_eq_parentProfileCoordinate_literalCount
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceNonempty :
      ∀ clause ∈ source.clauses, clause.literals ≠ [])
    (sourceWidth : source.erase.WidthAtMost 3)
    {metadata : ClauseMetadata Variable}
    (metadataMember : metadata ∈ formulaClauseMetadata source) :
    metadata.clause.literals.length =
      metadata.parentProfileCoordinate.literalCount := by
  rcases metadata_clause_length_eq_template
      source sourceNonempty sourceWidth metadataMember with
    ⟨templateClause, templateLookup, lengthEq⟩
  rw [ClauseMetadata.parentProfileCoordinate,
    ParentProfileCoordinate.literalCount, templateLookup]
  simpa using lengthEq

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
