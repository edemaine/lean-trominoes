/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapAppendIdxOfLookup
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorCandidateLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendClauseDescriptorLookup
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorBendEnumeration

/-! # Public representative descriptors of normalized bend clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Public first-occurrence selection assigns one normalized bend implication
its common translation-independent bend descriptor. -/
theorem representativeClauseDescriptor_eq_normalizedBend
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (taggedBend : RouteBend × Bool)
    (taggedBendMember : taggedBend ∈
      ((drawingRouteBends source.incidenceGraph).dedup).product
        [true, false]) :
    representativeClauseDescriptor source
        (normalizedBendClauseAt source taggedBend) =
      normalizedBendClauseDescriptorAt source taggedBend := by
  let prefixValues :=
    crossoverMetadataNormalizedClauses source ++
      carrierMetadataNormalizedClauses source
  let prefixOutputs :=
    crossoverMetadataClauseDescriptors source ++
      carrierMetadataClauseDescriptors source
  let suffixValues :=
    routedClauseMetadataNormalizedClauses source ++
      routedVariableMetadataNormalizedClauses source
  let suffixOutputs :=
    routedClauseMetadataClauseDescriptors source ++
      routedVariableMetadataClauseDescriptors source
  have bendMember : normalizedBendClauseAt source taggedBend ∈
      bendMetadataNormalizedClauses source := by
    rw [bendMetadataNormalizedClauses_eq_map_taggedBends]
    exact List.mem_map.mpr ⟨taggedBend, taggedBendMember, rfl⟩
  have bendPrefixLength : (bendMetadataClauseDescriptors source).length =
      (bendMetadataNormalizedClauses source).length := by
    simp [bendMetadataClauseDescriptors,
      bendMetadataNormalizedClauses]
  have bendLookup :=
    bendMetadataClauseDescriptors_getElem?_idxOf_normalized
      source taggedBend taggedBendMember
  have suffixLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_mem
      (bendMetadataNormalizedClauses source) suffixValues
      (bendMetadataClauseDescriptors source) suffixOutputs
      (normalizedBendClauseAt source taggedBend)
      (normalizedBendClauseDescriptorAt source taggedBend)
      bendPrefixLength bendMember bendLookup
  have nonCrossoverMember : normalizedBendClauseAt source taggedBend ∈
      nonCrossoverMetadataNormalizedClauses source := by
    rw [nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr bendMember))
  have notCrossover : normalizedBendClauseAt source taggedBend ∉
      crossoverMetadataNormalizedClauses source := by
    intro crossoverMember
    exact (List.disjoint_left.mp
      (crossoverMetadataNormalizedClauses_disjoint_nonCrossover
        source wellFormed degree isLocal))
      crossoverMember nonCrossoverMember
  have notCarrier : normalizedBendClauseAt source taggedBend ∉
      carrierMetadataNormalizedClauses source := by
    intro carrierMember
    exact (List.disjoint_left.mp
      (carrierMetadataNormalizedClauses_disjoint_bend source))
      carrierMember bendMember
  have prefixNotMember : normalizedBendClauseAt source taggedBend ∉
      prefixValues := by
    intro prefixMember
    rcases List.mem_append.mp prefixMember with
      crossoverMember | carrierMember
    · exact notCrossover crossoverMember
    · exact notCarrier carrierMember
  have prefixLength : prefixOutputs.length = prefixValues.length := by
    simp [prefixOutputs, prefixValues,
      crossoverMetadataClauseDescriptors,
      carrierMetadataClauseDescriptors,
      crossoverMetadataNormalizedClauses,
      carrierMetadataNormalizedClauses]
  have globalLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_not_mem
      prefixValues
      (bendMetadataNormalizedClauses source ++ suffixValues)
      prefixOutputs
      (bendMetadataClauseDescriptors source ++ suffixOutputs)
      (normalizedBendClauseAt source taggedBend)
      (normalizedBendClauseDescriptorAt source taggedBend)
      prefixLength prefixNotMember suffixLookup
  have normalizedEq : normalizedClauses source =
      prefixValues ++
        (bendMetadataNormalizedClauses source ++ suffixValues) := by
    rw [normalizedClauses_eq_crossover_append_nonCrossover,
      nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [prefixValues, suffixValues, List.append_assoc]
  have candidatesEq : metadataClauseDescriptorCandidates source =
      prefixOutputs ++
        (bendMetadataClauseDescriptors source ++ suffixOutputs) := by
    rw [metadataClauseDescriptorCandidates_eq_families]
    unfold familyMetadataClauseDescriptors
    simp only [prefixOutputs, suffixOutputs, List.append_assoc]
  rw [← normalizedEq, ← candidatesEq] at globalLookup
  have normalizedMember : normalizedBendClauseAt source taggedBend ∈
      normalizedClauses source := by
    rw [normalizedEq]
    exact List.mem_append_right _
      (List.mem_append_left _ bendMember)
  have clauseLookup :
      (normalizedClauses source)[
          (normalizedClauses source).idxOf
            (normalizedBendClauseAt source taggedBend)]? =
        some (normalizedBendClauseAt source taggedBend) :=
    List.getElem?_idxOf normalizedMember
  have candidateLookup :=
    metadataClauseDescriptorCandidates_getElem?_eq source
      (normalizedBendClauseAt source taggedBend)
      ((normalizedClauses source).idxOf
        (normalizedBendClauseAt source taggedBend)) clauseLookup
  unfold representativeClauseDescriptor
  exact Option.some.inj (candidateLookup.symm.trans globalLookup)

/-- Untranslated routed bends in numeric route order. -/
def baseRouteBends
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List RouteBend :=
  (numericRouteDescriptors source).flatMap fun descriptor =>
    routeBends descriptor.edgeIndex (0, 0) descriptor.route

/-- Every untranslated base bend occurs in the physical neighboring bend
enumeration. -/
theorem baseRouteBends_subset_drawing
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    baseRouteBends source ⊆
      (drawingRouteBends source.incidenceGraph).dedup := by
  intro routeBend routeBendMember
  rw [incidenceGraph_drawingRouteBends_dedup,
    incidenceGraph_drawingRouteBends_eq_numeric]
  unfold baseRouteBends at routeBendMember
  rcases List.mem_flatMap.mp routeBendMember with
    ⟨descriptor, descriptorMember, routeBendMember⟩
  apply List.mem_flatMap.mpr
  refine ⟨descriptor, descriptorMember, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(0, 0), ?_, routeBendMember⟩
  native_decide

/-- The canonical bend links are exactly the wrapped normalizations of the
untranslated base bend scan. -/
theorem baseBendNormalizedLinks_eq_map_baseRouteBends
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    baseBendNormalizedLinks source =
      (baseRouteBends source).map
        (wrappedNormalizedRouteBendLink source) := by
  unfold baseBendNormalizedLinks baseRouteBends
    translatedRouteBendNormalizedLinks
  rw [List.map_flatMap]

/-- The canonical base bend clauses are the untranslated bend/direction scan
mapped through its normalized clauses. -/
theorem baseBendNormalizedClauses_eq_map_baseTaggedBends
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    baseBendNormalizedClauses source =
      ((baseRouteBends source).product [true, false]).map
        (normalizedBendClauseAt source) := by
  unfold baseBendNormalizedClauses
  rw [baseBendNormalizedLinks_eq_map_baseRouteBends]
  induction baseRouteBends source with
  | nil => rfl
  | cons routeBend routeBends induction =>
      change
        normalizedBendClauseAt source (routeBend, true) ::
            normalizedBendClauseAt source (routeBend, false) ::
            ((((routeBends.map
              (wrappedNormalizedRouteBendLink source)).product
                [true, false]).map PeriodicEquality.normalizedClause)) =
          normalizedBendClauseAt source (routeBend, true) ::
            normalizedBendClauseAt source (routeBend, false) ::
            ((routeBends.product [true, false]).map
              (normalizedBendClauseAt source))
      rw [induction]

/-- Finite descriptor stream of the untranslated base bend scan. -/
def baseBendClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  ((baseRouteBends source).product [true, false]).map
    (normalizedBendClauseDescriptorAt source)

/-- The base bend descriptor stream is one fixed two-token block for each
untranslated bend. -/
theorem baseBendClauseDescriptors_eq_canonicalBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    baseBendClauseDescriptors source =
      (baseRouteBends source).flatMap fun routeBend =>
        canonicalBendDescriptorBlock routeBend.incomingPort
          routeBend.outgoingPort false := by
  unfold baseBendClauseDescriptors
  induction baseRouteBends source with
  | nil => rfl
  | cons routeBend routeBends induction =>
      change
        normalizedBendClauseDescriptorAt source (routeBend, true) ::
            normalizedBendClauseDescriptorAt source (routeBend, false) ::
            ((routeBends.product [true, false]).map
              (normalizedBendClauseDescriptorAt source)) =
          canonicalBendDescriptorBlock routeBend.incomingPort
              routeBend.outgoingPort false ++
            routeBends.flatMap (fun routeBend =>
              canonicalBendDescriptorBlock routeBend.incomingPort
                routeBend.outgoingPort false)
      rw [induction]
      unfold normalizedBendClauseDescriptorAt
        canonicalBendDescriptorBlock
      rw [metadataClauseDescriptor_bendClauseMetadataAt_eq,
        metadataClauseDescriptor_bendClauseMetadataAt_eq,
        bendLinkNextSlice_eq_false]
      rfl

/-- Mapping public representative selection over the canonical base bend
clauses yields the exact untranslated bend descriptor stream. -/
theorem baseBendNormalizedClauses_map_representative_eq_descriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    (baseBendNormalizedClauses source).map
        (representativeClauseDescriptor source) =
      baseBendClauseDescriptors source := by
  rw [baseBendNormalizedClauses_eq_map_baseTaggedBends]
  unfold baseBendClauseDescriptors
  rw [List.map_map]
  apply List.map_congr_left
  intro taggedBend taggedBendMember
  simp only [Function.comp_apply]
  apply representativeClauseDescriptor_eq_normalizedBend
    source wellFormed degree isLocal taggedBend
  rcases List.mem_product.mp taggedBendMember with
    ⟨routeBendMember, directionMember⟩
  exact List.mem_product.mpr
    ⟨baseRouteBends_subset_drawing source routeBendMember,
      directionMember⟩

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
