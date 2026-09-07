/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationMetadataRouteSourceIndexedListSemantics

/-! # Actual literal atoms selected by source-indexed polarity operations -/

namespace LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicCNF.ClauseProfilePolarityRouteOperation

/-- Decode a polarity operation at its source occurrence. Fresh atoms retain
the exact source literal, as required by the semantic normalization. -/
def SourceIndexedDescriptor.atom? {Variable : Type*}
    (descriptor : SourceIndexedDescriptor) (source : PeriodicCNF Variable) :
    Option (PolarityNormalizedVariable Variable) :=
  (source.clauses[descriptor.sourceClauseIndex]?).bind fun clause =>
    (clause[descriptor.sourceLiteralIndex]?).map fun literal =>
      match descriptor.operation with
      | .compatible | .complementOriginal => .inl literal.atom
      | .incompatible | .complementFresh =>
          .inr ((descriptor.sourceClauseIndex, descriptor.sourceLiteralIndex), literal)

private theorem flatMap_filterMap {α β γ : Type*}
    (source : List α) (select : α → Option β) (emit : β → List γ) :
    (source.filterMap select).flatMap emit =
      source.flatMap (fun item => (select item).toList.flatMap emit) := by
  induction source with
  | nil => rfl
  | cons item rest ih =>
      cases selected : select item <;> simp [selected, ih]

/-- Every operation in one clause's schedule decodes to the actual output
atom, including both occurrences of each fresh complement variable. -/
theorem indexedDescriptors_map_atom? {Variable : Type*}
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    (indexedDescriptors (clause.map PeriodicLiteral.value)).map
        (fun descriptor => (sourceIndexedDescriptorOf clauseIndex descriptor).atom? source) =
      (PeriodicOneInThreePolarityNormalization.clauseClauses clauseIndex clause).flatMap
        (fun output => output.map (fun literal => some literal.atom)) := by
  have normalized :
      clause.zipIdx.map (fun tagged =>
        (sourceIndexedDescriptorOf clauseIndex
          (normalizedIndexedDescriptor (tagged.1.value, tagged.2))).atom? source) =
      (PeriodicOneInThreePolarityNormalization.normalizeClause clauseIndex clause).map
        (fun literal => some literal.atom) := by
    unfold PeriodicOneInThreePolarityNormalization.normalizeClause
      PeriodicOneInThreePolarityNormalization.normalizeClauseFrom
    rw [List.map_map]
    apply List.map_congr_left
    intro tagged member
    have literalLookup := List.mem_zipIdx_iff_getElem?.mp member
    by_cases compatible : tagged.1.value =
        PeriodicOneInThreePolarityNormalization.normalizedPolarity tagged.2 <;>
      simp [SourceIndexedDescriptor.atom?, sourceIndexedDescriptorOf,
        normalizedIndexedDescriptor, clauseLookup, literalLookup, compatible,
        PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity_eq_semantic,
        PeriodicOneInThreePolarityNormalization.normalizeLiteral,
        PeriodicOneInThreePolarityNormalization.liftLiteral,
        PeriodicOneInThreePolarityNormalization.complementLiteral]
  have complements :
      clause.zipIdx.flatMap (fun tagged =>
        (complementIndexedDescriptorBlock (tagged.1.value, tagged.2)).map
          (fun descriptor =>
            (sourceIndexedDescriptorOf clauseIndex descriptor).atom? source)) =
      (PeriodicOneInThreePolarityNormalization.complementClauses clauseIndex clause).flatMap
        (fun output => output.map (fun literal => some literal.atom)) := by
    unfold PeriodicOneInThreePolarityNormalization.complementClauses
      PeriodicOneInThreePolarityNormalization.complementClausesFrom
    rw [flatMap_filterMap]
    apply List.flatMap_congr
    intro tagged member
    have literalLookup := List.mem_zipIdx_iff_getElem?.mp member
    by_cases compatible : tagged.1.value =
        PeriodicOneInThreePolarityNormalization.normalizedPolarity tagged.2 <;>
      simp [complementIndexedDescriptorBlock, compatible,
        PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity_eq_semantic,
        SourceIndexedDescriptor.atom?, sourceIndexedDescriptorOf,
        clauseLookup, literalLookup,
        PeriodicOneInThreePolarityNormalization.complementClause,
        PeriodicOneInThreePolarityNormalization.complementFalseLiteral,
        PeriodicOneInThreePolarityNormalization.originalFalseLiteral]
  simp only [indexedDescriptors, List.map_append, List.zipIdx_map,
    List.map_map, List.map_flatMap, List.flatMap_map, Function.comp_def,
    Prod.map, id_eq, PeriodicOneInThreePolarityNormalization.clauseClauses,
    List.flatMap_cons]
  rw [normalized, complements]

/-- Decoding the complete schedule gives the actual normalized atom column
in clause-major, literal-minor order; no occurrence lookup is missing. -/
theorem sourceIndexedDescriptors_map_atom? {Variable : Type*}
    (source : PeriodicCNF Variable) :
    (source.clauses.zipIdx.flatMap fun tagged =>
      (indexedDescriptors (tagged.1.map PeriodicLiteral.value)).map
        (sourceIndexedDescriptorOf tagged.2)).map
          (fun descriptor => descriptor.atom? source) =
      (PeriodicOneInThreePolarityNormalization.formula source).clauses.flatMap
        (fun clause => clause.map (fun literal => some literal.atom)) := by
  simp only [List.map_flatMap, List.map_map,
    PeriodicOneInThreePolarityNormalization.formula, List.flatMap_assoc]
  apply List.flatMap_congr
  intro tagged member
  exact indexedDescriptors_map_atom? source tagged.2 tagged.1
    (List.mem_zipIdx_iff_getElem?.mp member)

/-- The exact route-block schedule also identifies every actual routed atom.
Decoding uses the refined source literal; the final gauge preserves its atom. -/
theorem exactMetadataRouteBlocks_map_atom? {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    (exactMetadataRouteBlocks source sourcePlacement sourceRoutes).map
        (fun block => block.sourceIndexedDescriptor.atom?
          (refinedSource source sourcePlacement).erase) =
      (formula source sourcePlacement sourceRoutes).erase.clauses.flatMap
        (fun clause => clause.map (fun literal => some literal.atom)) := by
  have schedule :=
    (exactMetadataRouteBlocks_map_sourceIndexedDescriptor
      source sourcePlacement sourceRoutes).trans
      (formulaClauseMetadata_flatMap_sourceIndexedDescriptor
        (rawPositions sourcePlacement sourceRoutes)
        (refinedSource source sourcePlacement))
  have atoms := congrArg
    (List.map (fun descriptor => descriptor.atom?
      (refinedSource source sourcePlacement).erase)) schedule
  rw [List.map_map] at atoms
  calc
    _ = _ := atoms
    _ = (PeriodicOneInThreePolarityNormalization.formula
          (refinedSource source sourcePlacement).erase).clauses.flatMap
            (fun clause => clause.map (fun literal => some literal.atom)) := by
      simpa only [PositionedPeriodicCNF.erase, List.zipIdx_map,
        List.flatMap_map, List.map_map, Function.comp_def, Prod.map, id_eq] using
        sourceIndexedDescriptors_map_atom? (refinedSource source sourcePlacement).erase
    _ = _ := by
      rw [erase_formula]
      simp only [PeriodicCNF.variableGauge, PeriodicClause.variableGauge,
        List.flatMap_map, List.map_map, Function.comp_def,
        PeriodicLiteral.variableGauge_atom]

end LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
