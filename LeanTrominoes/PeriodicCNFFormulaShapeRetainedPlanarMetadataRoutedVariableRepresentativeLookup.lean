/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapAppendIdxOfLookup
import LeanTrominoes.ListMapIdxOfPreimage
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendRoutedVariableNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseRoutedVariableNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableClauseData

/-! # Raw metadata representative of a normalized routed variable -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A normalized routed-variable implication selects routed-variable
metadata at its first occurrence in the complete five-family presentation.
The selected record retains its exact site, active arm link, and implication
direction. -/
theorem exists_routedVariableMetadata_global_lookup_of_normalized_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember :
      clause ∈ routedVariableMetadataNormalizedClauses source) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf clause]? = some metadata ∧
      normalizedClause source metadata = clause ∧
      ∃ (site : VariableRouteSite Variable) (armIndex : Nat)
          (arm : DuplicatorArm)
          (link : EqualityLink (PlanarSATNode Variable))
          (forward : Bool),
        site ∈ drawingVariableRouteSites source ∧
        (link, armIndex) ∈ (routedVariableLinksAt source site).zipIdx ∧
        arm = link.first.duplicatorArm ∧
        metadata = routedVariableClauseMetadataAt
          site armIndex arm link forward := by
  have mappedMember : clause ∈
      (drawingPlanarSATRoutedVariableClauseMetadata source).map
        (normalizedClause source) := by
    exact clauseMember
  rcases IndexedListScan.exists_getElem?_idxOf_map
      (drawingPlanarSATRoutedVariableClauseMetadata source)
      (normalizedClause source) clause mappedMember with
    ⟨metadata, routedLookup, normalizedEq, metadataMember⟩
  have sourceWitness :
      ∃ (site : VariableRouteSite Variable) (armIndex : Nat)
          (arm : DuplicatorArm)
          (link : EqualityLink (PlanarSATNode Variable))
          (forward : Bool),
        site ∈ drawingVariableRouteSites source ∧
        (link, armIndex) ∈ (routedVariableLinksAt source site).zipIdx ∧
        arm = link.first.duplicatorArm ∧
        metadata = routedVariableClauseMetadataAt
          site armIndex arm link forward := by
    unfold drawingPlanarSATRoutedVariableClauseMetadata at metadataMember
    rcases List.mem_flatMap.mp metadataMember with
      ⟨site, siteMember, metadataMember⟩
    rcases List.mem_flatMap.mp metadataMember with
      ⟨taggedLink, taggedLinkMember, metadataMember⟩
    rw [drawingPlanarSATRoutedVariableClauseMetadataFor_eq_pair]
      at metadataMember
    simp only [List.mem_cons, List.not_mem_nil, or_false]
      at metadataMember
    rcases metadataMember with metadataEq | metadataEq
    · exact ⟨site, taggedLink.2, taggedLink.1.first.duplicatorArm,
        taggedLink.1, true, siteMember, taggedLinkMember, rfl, metadataEq⟩
    · exact ⟨site, taggedLink.2, taggedLink.1.first.duplicatorArm,
        taggedLink.1, false, siteMember, taggedLinkMember, rfl, metadataEq⟩
  let prefixValues :=
    crossoverMetadataNormalizedClauses source ++
      carrierMetadataNormalizedClauses source ++
        bendMetadataNormalizedClauses source ++
          routedClauseMetadataNormalizedClauses source
  let prefixMetadata :=
    drawingPlanarSATCrossoverClauseMetadata
        (Variable := Variable) source.incidenceGraph ++
      retainedDrawingPlanarSATCarrierClauseMetadata
          (Variable := Variable) source.incidenceGraph ++
        drawingPlanarSATBendClauseMetadata
            (Variable := Variable) source.incidenceGraph ++
          drawingPlanarSATRoutedClauseMetadata source
  have nonCrossoverMember :
      clause ∈ nonCrossoverMetadataNormalizedClauses source := by
    rw [nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [List.mem_append]
    exact Or.inr clauseMember
  have notCrossover :
      clause ∉ crossoverMetadataNormalizedClauses source := by
    intro crossoverMember
    exact (List.disjoint_left.mp
      (crossoverMetadataNormalizedClauses_disjoint_nonCrossover
        source wellFormed degree isLocal))
      crossoverMember nonCrossoverMember
  have notCarrier :
      clause ∉ carrierMetadataNormalizedClauses source := by
    intro carrierMember
    exact (List.disjoint_left.mp
      (carrierMetadataNormalizedClauses_disjoint_routedVariable source))
      carrierMember clauseMember
  have notBend :
      clause ∉ bendMetadataNormalizedClauses source := by
    intro bendMember
    exact (List.disjoint_left.mp
      (bendMetadataNormalizedClauses_disjoint_routedVariable source))
      bendMember clauseMember
  have notRoutedClause :
      clause ∉ routedClauseMetadataNormalizedClauses source := by
    intro routedClauseMember
    exact (List.disjoint_left.mp
      (routedClauseMetadataNormalizedClauses_disjoint_routedVariable
        source)) routedClauseMember clauseMember
  have prefixNotMember : clause ∉ prefixValues := by
    intro prefixMember
    change clause ∈
      ((crossoverMetadataNormalizedClauses source ++
          carrierMetadataNormalizedClauses source) ++
        bendMetadataNormalizedClauses source) ++
          routedClauseMetadataNormalizedClauses source at prefixMember
    rcases List.mem_append.mp prefixMember with
      prefixBeforeRouted | routedMember
    · rcases List.mem_append.mp prefixBeforeRouted with
        prefixBeforeBend | bendMember
      · rcases List.mem_append.mp prefixBeforeBend with
          crossoverMember | carrierMember
        · exact notCrossover crossoverMember
        · exact notCarrier carrierMember
      · exact notBend bendMember
    · exact notRoutedClause routedMember
  have prefixLength : prefixMetadata.length = prefixValues.length := by
    simp [prefixMetadata, prefixValues,
      crossoverMetadataNormalizedClauses,
      carrierMetadataNormalizedClauses,
      bendMetadataNormalizedClauses,
      routedClauseMetadataNormalizedClauses]
  have globalLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_not_mem
      prefixValues
      (routedVariableMetadataNormalizedClauses source)
      prefixMetadata
      (drawingPlanarSATRoutedVariableClauseMetadata source)
      clause metadata prefixLength prefixNotMember routedLookup
  have normalizedClausesEq :
      normalizedClauses source =
        prefixValues ++ routedVariableMetadataNormalizedClauses source := by
    rw [normalizedClauses_eq_crossover_append_nonCrossover,
      nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [prefixValues, List.append_assoc]
  rw [← normalizedClausesEq] at globalLookup
  have metadataEq :
      retainedDrawingPlanarSATClauseMetadata source =
        prefixMetadata ++
          drawingPlanarSATRoutedVariableClauseMetadata source := by
    simp [retainedDrawingPlanarSATClauseMetadata,
      prefixMetadata, List.append_assoc]
  rw [← metadataEq] at globalLookup
  exact ⟨metadata, globalLookup, normalizedEq, sourceWitness⟩

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
