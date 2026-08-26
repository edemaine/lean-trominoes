/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingClauseSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorMetadataData
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseDirectQueryPacking
import LeanTrominoes.RetainedAngularFanFinalDirectSourceDirectionQuerySemantics

/-! # Direct final clause queries from canonical metadata -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- If canonical direct metadata normalizes to a genuine width-three final
clause and every raw lookup selects the declared atlas kind at its literal
index, then the exact final clause query is the stable direct replacement
of that metadata record's descriptor. -/
theorem retainedFinalCopiedClauseQueryOfLiterals_eq_directOfMetadataDescriptor
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    (clauseIndex : Nat)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseLookup :
      (deduplicatedClauses formula)[clauseIndex]? = some clause)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataLookup :
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some metadata)
    (normalizedEq : normalizedClause formula metadata = clause)
    (directCases :
      (∃ crossing localClauseIndex,
          metadata.source = .crossover crossing localClauseIndex) ∨
        (∃ site,
          metadata.source = .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex))
    (kind : RetainedDirectClauseKind)
    (rawChoiceShape :
      ∀ literalIndex rawChoice,
        retainedDirectSourceRouteChoice?
            formula metadata.source literalIndex = some rawChoice →
          rawChoice.kind = kind ∧
            rawChoice.index.val = literalIndex) :
    retainedFinalCopiedClauseQueryOfLiterals
        formula clauseIndex clause =
      RetainedFinalCopiedClauseQuery.directOfToken kind
        (metadataClauseDescriptor formula metadata) := by
  have clauseMember :
      clause ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.clauses := by
    rw [positionedSource_erase_clauses_eq]
    exact List.mem_of_getElem? clauseLookup
  have clauseNonempty : clause ≠ [] :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty clause clauseMember
  have clauseWidth : clause.length ≤ 3 :=
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_widthAtMostThree
      formula sourceWidth clause clauseMember
  unfold metadataClauseDescriptor
  simp only [RetainedFinalCopiedClauseQuery.directOfToken]
  apply retainedFinalCopiedClauseQueryOfLiterals_eq_directOfProfile
    formula clauseIndex clause kind
  · exact clauseNonempty
  · rw [FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause_taggedLiterals
      _ _ _ (by simpa [normalizedEq] using clauseNonempty)
      (by simpa [normalizedEq] using clauseWidth)]
    unfold FormulaShapeDirectionOrdering.annotatedLiterals
    rw [List.map_map]
    change
      (normalizedClause formula metadata).zipIdx.map
          (fun taggedLiteral =>
            FormulaShapeDirectionOrdering.literalProfile taggedLiteral.1) =
        clause.map FormulaShapeDirectionOrdering.literalProfile
    calc
      _ = ((normalizedClause formula metadata).zipIdx.map Prod.fst).map
            FormulaShapeDirectionOrdering.literalProfile := by
          rw [List.map_map]
          apply List.map_congr_left
          intro taggedLiteral _taggedLiteralMember
          rfl
      _ = _ := by
          rw [List.zipIdx_map_fst, normalizedEq]
  · intro taggedLiteral taggedLiteralMember
    rcases
        exists_finalDirectChoiceRaw_of_clause_lookup_metadata_direct
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex clause clauseLookup
          taggedLiteral.1 taggedLiteral.2 taggedLiteralMember
          metadata metadataLookup directCases with
      ⟨choice, rawChoice, choiceLookup, rawLookup, choiceEq⟩
    have rawShape :=
      rawChoiceShape taggedLiteral.2 rawChoice rawLookup
    let query := rawChoice.normalizedDirectionQuery
    refine ⟨query, ?_, ?_, ?_⟩
    · unfold retainedFinalCopiedSourceDirectionQuery
      rw [choiceLookup]
      simp only
      rw [choiceEq]
      rfl
    · exact rawShape.1
    · exact rawShape.2

end PeriodicEightOccurrenceSplit
end LeanTrominoes
