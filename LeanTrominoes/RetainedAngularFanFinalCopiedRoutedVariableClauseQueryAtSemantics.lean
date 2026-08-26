/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableDescriptorSemanticsAt
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizedFamilyData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizationArmClassification
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNextSliceSemantics
import LeanTrominoes.RetainedAngularFanDirectSourceRoutedVariableChoiceShape
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseDirectMetadataQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalRoutedVariableMetadataSemantics

/-! # Exact final query for one routed-variable implication -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- The exact final query of one normalized routed-variable implication is
the stable direct query classified by that normalized link's physical arm
and implication direction. -/
theorem retainedFinalCopiedClauseQueryOfLiterals_eq_routedVariable_of_link
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    (clauseIndex : Nat)
    (taggedLink : PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable) × Bool)
    (taggedLinkMember : taggedLink ∈
      ((drawingRoutedVariableLinks formula).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization formula))).product
        [true, false])
    (clauseLookup :
      (deduplicatedClauses formula)[clauseIndex]? =
        some (PeriodicEquality.normalizedClause taggedLink)) :
    retainedFinalCopiedClauseQueryOfLiterals formula clauseIndex
        (PeriodicEquality.normalizedClause taggedLink) =
      retainedFinalDirectRoutedVariableClauseQuery
        (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
        false taggedLink.2 := by
  let clause := PeriodicEquality.normalizedClause taggedLink
  have graphWellFormed : formula.incidenceGraph.IsWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed formula
  have graphDegree : formula.incidenceGraph.DegreeAtMost 3 :=
    PeriodicCNF.incidenceGraph_degreeAtMost
      sourceWidth sourceOccurrences
  have graphLocal : formula.incidenceGraph.IsLocal :=
    PeriodicCNF.incidenceGraph_isLocal sourceLocal
  have routedVariableMember :
      clause ∈ routedVariableMetadataNormalizedClauses formula := by
    rw [routedVariableMetadataNormalizedClauses_eq_normalizedFormulaClauses,
      PeriodicEquality.normalizedFormulaClauses_eq]
    exact List.mem_map.mpr ⟨taggedLink, taggedLinkMember, rfl⟩
  rcases exists_finalRoutedVariableMetadata_of_clause_lookup
      formula graphWellFormed graphDegree graphLocal
      clauseIndex clause clauseLookup routedVariableMember with
    ⟨metadata, metadataLookup, normalizedEq, site, armIndex, arm,
      link, forward, siteMember, selectedLinkMember, armEq, metadataEq⟩
  subst metadata
  have linkMember : link ∈ drawingRoutedVariableLinks formula := by
    unfold drawingRoutedVariableLinks
    exact List.mem_flatMap.mpr
      ⟨site, siteMember,
        List.fst_mem_of_mem_zipIdx selectedLinkMember⟩
  have selectedNormalizedEq :
      PeriodicEquality.normalizedClause
          (PeriodicEquality.normalizeLink
            (externalWrappedVariableNormalization formula) link,
            forward) =
        PeriodicEquality.normalizedClause taggedLink := by
    rw [← normalizedClause_routedVariableClauseMetadataAt_eq
      formula site armIndex arm link forward]
    exact normalizedEq
  have selectedPairEq :
      (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization formula) link,
        forward) = taggedLink :=
    PeriodicEquality.normalizedClause_injective selectedNormalizedEq
  have normalizedLinkEq :
      PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization formula) link =
        taggedLink.1 :=
    congrArg Prod.fst selectedPairEq
  have forwardEq : forward = taggedLink.2 :=
    congrArg Prod.snd selectedPairEq
  have targetArmEq :
      wrappedNormalizedRoutedVariableLinkArm taggedLink.1 = arm := by
    rw [← normalizedLinkEq,
      wrappedNormalizedRoutedVariableLinkArm_normalizeLink
        formula link linkMember]
    exact armEq.symm
  have nextSliceEq :
      routedVariableLinkNextSlice formula link = false :=
    routedVariableLinkNextSlice_eq_false
      formula graphWellFormed graphLocal site link
        (List.fst_mem_of_mem_zipIdx selectedLinkMember)
  let localClauseIndex := if forward then 0 else 1
  have localClauseIndexFinEq
      (localClauseIndexLt : localClauseIndex < 2) :
      (⟨localClauseIndex, localClauseIndexLt⟩ : Fin 2) =
        retainedFinalDirectDuplicatorClauseIndex forward := by
    cases forward <;> rfl
  have queryEq :=
    retainedFinalCopiedClauseQueryOfLiterals_eq_directOfMetadataDescriptor
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex clause clauseLookup
      (routedVariableClauseMetadataAt
        site armIndex arm link forward)
      metadataLookup normalizedEq
      (Or.inr (Or.inr
        ⟨site, armIndex, arm, link, localClauseIndex, rfl⟩))
      (.duplicator arm
        (retainedFinalDirectDuplicatorClauseIndex forward)) (by
          intro literalIndex rawChoice rawLookup
          rcases
              retainedDirectSourceRouteChoice?_routedVariable_eq_some_iff_shape
                formula site armIndex arm link localClauseIndex
                literalIndex rawChoice rawLookup with
            ⟨localClauseIndexLt, _literalIndexLt, rawChoiceEq⟩
          subst rawChoice
          constructor
          · change
              RetainedDirectClauseKind.duplicator arm
                  ⟨localClauseIndex, localClauseIndexLt⟩ =
                RetainedDirectClauseKind.duplicator arm
                  (retainedFinalDirectDuplicatorClauseIndex forward)
            exact congrArg
              (RetainedDirectClauseKind.duplicator arm)
              (localClauseIndexFinEq localClauseIndexLt)
          · rfl)
  calc
    retainedFinalCopiedClauseQueryOfLiterals formula clauseIndex clause =
        RetainedFinalCopiedClauseQuery.directOfToken
          (.duplicator arm
            (retainedFinalDirectDuplicatorClauseIndex forward))
          (metadataClauseDescriptor formula
            (routedVariableClauseMetadataAt
              site armIndex arm link forward)) :=
      queryEq
    _ = RetainedFinalCopiedClauseQuery.directOfToken
          (.duplicator arm
            (retainedFinalDirectDuplicatorClauseIndex forward))
          (routedVariableClauseDescriptor arm false forward) := by
      rw [metadataClauseDescriptor_routedVariableClauseMetadataAt_eq,
        nextSliceEq]
    _ = retainedFinalDirectRoutedVariableClauseQuery
          arm false forward := by
      rfl
    _ = retainedFinalDirectRoutedVariableClauseQuery
          (wrappedNormalizedRoutedVariableLinkArm taggedLink.1)
          false taggedLink.2 := by
      rw [targetArmEq, ← forwardEq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
