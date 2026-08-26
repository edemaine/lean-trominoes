/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendClauseData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendDescriptorSemanticsAt
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNextSliceSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNormalizedFamilyDeduplication

/-! # First-occurrence lookup of normalized bend descriptors -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The normalized implication clause selected by one physical routed bend
and direction. -/
def normalizedBendClauseAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool) :
    PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) :=
  PeriodicEquality.normalizedClause
    (wrappedNormalizedRouteBendLink source taggedBend.1,
      taggedBend.2)

/-- The metadata candidate descriptor selected by one physical routed bend
and direction. -/
def normalizedBendClauseDescriptorAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool) :
    FormulaShapeDirectionOrdering.Token :=
  metadataClauseDescriptor source
    (bendClauseMetadataAt source.incidenceGraph
      taggedBend.1 taggedBend.2)

/-- Equal wrapped normalized bend links determine equal incoming and outgoing
corner ports, even when the physical bends use different translations. -/
theorem routeBend_ports_eq_of_wrappedNormalizedLink_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (first second : RouteBend)
    (linksEq : wrappedNormalizedRouteBendLink source first =
      wrappedNormalizedRouteBendLink source second) :
    first.incomingPort = second.incomingPort ∧
      first.outgoingPort = second.outgoingPort := by
  have rawEq := (carrierWrappedNormalizeLink_eq_iff source
    (first.equalityLink source.incidenceGraph)
    (second.equalityLink source.incidenceGraph)).mp linksEq
  have firstEndpointEq := congrArg
    PeriodicEquality.NormalizedLink.first rawEq
  have secondEndpointEq := congrArg
    PeriodicEquality.NormalizedLink.second rawEq
  simp only [RouteBend.normalize_equalityLink_first]
    at firstEndpointEq
  simp only [RouteBend.normalize_equalityLink_second]
    at secondEndpointEq
  have incomingIndexedEq : first.incomingTerminal.indexed =
      second.incomingTerminal.indexed :=
    (PeriodicCarrierNode.terminal.inj firstEndpointEq).1
  have outgoingIndexedEq : first.outgoingTerminal.indexed =
      second.outgoingTerminal.indexed :=
    (PeriodicCarrierNode.terminal.inj secondEndpointEq).1
  rcases first with
    ⟨firstRoute, firstSegment, firstTranslate,
      firstStart, firstBend, firstFinish⟩
  rcases second with
    ⟨secondRoute, secondSegment, secondTranslate,
      secondStart, secondBend, secondFinish⟩
  simp [RouteBend.incomingTerminal, RouteBend.outgoingTerminal,
    RouteBend.incomingPort, RouteBend.outgoingPort] at incomingIndexedEq outgoingIndexedEq ⊢
  simp_all

/-- The normalized bend clause family is the physical bend/direction
presentation mapped through its pointwise normal form. -/
theorem bendMetadataNormalizedClauses_eq_map_taggedBends
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    bendMetadataNormalizedClauses source =
      (((drawingRouteBends source.incidenceGraph).dedup).product
        [true, false]).map (normalizedBendClauseAt source) := by
  rw [bendMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq]
  unfold drawingRouteBendLinks
  simp only [List.map_map, Function.comp_def]
  induction (drawingRouteBends source.incidenceGraph).dedup with
  | nil => rfl
  | cons routeBend routeBends induction =>
      change
        normalizedBendClauseAt source (routeBend, true) ::
            normalizedBendClauseAt source (routeBend, false) ::
            (((routeBends.map (fun routeBend =>
              PeriodicEquality.normalizeLink
                (carrierWrappedVariableNormalization source)
                (routeBend.equalityLink source.incidenceGraph))).product
                [true, false]).map PeriodicEquality.normalizedClause) =
          normalizedBendClauseAt source (routeBend, true) ::
            normalizedBendClauseAt source (routeBend, false) ::
            ((routeBends.product [true, false]).map
              (normalizedBendClauseAt source))
      rw [induction]

/-- The bend candidate descriptor family is the same physical
bend/direction presentation mapped through its metadata descriptor. -/
theorem bendMetadataClauseDescriptors_eq_map_taggedBends
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    bendMetadataClauseDescriptors source =
      (((drawingRouteBends source.incidenceGraph).dedup).product
        [true, false]).map
          (normalizedBendClauseDescriptorAt source) := by
  rw [bendMetadataClauseDescriptors_eq_flatMap_bendBlocks]
  induction (drawingRouteBends source.incidenceGraph).dedup with
  | nil => rfl
  | cons routeBend routeBends induction =>
      rw [List.flatMap_cons, bendClauseDescriptors_eq_pair, induction]
      rfl

/-- Looking up the descriptor at the first local occurrence of a normalized
bend implication returns the common descriptor of that bend orbit. -/
theorem bendMetadataClauseDescriptors_getElem?_idxOf_normalized
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool)
    (taggedBendMember : taggedBend ∈
      ((drawingRouteBends source.incidenceGraph).dedup).product
        [true, false]) :
    (bendMetadataClauseDescriptors source)[
        (bendMetadataNormalizedClauses source).idxOf
          (normalizedBendClauseAt source taggedBend)]? =
      some (normalizedBendClauseDescriptorAt source taggedBend) := by
  rw [bendMetadataNormalizedClauses_eq_map_taggedBends,
    bendMetadataClauseDescriptors_eq_map_taggedBends]
  let taggedBends :=
    ((drawingRouteBends source.incidenceGraph).dedup).product
      [true, false]
  change (taggedBends.map (normalizedBendClauseDescriptorAt source))[
      (taggedBends.map (normalizedBendClauseAt source)).idxOf
        (normalizedBendClauseAt source taggedBend)]? = _
  have normalizedClauseMember : normalizedBendClauseAt source taggedBend ∈
      taggedBends.map (normalizedBendClauseAt source) :=
    List.mem_map.mpr ⟨taggedBend, taggedBendMember, rfl⟩
  have clauseLookup := List.getElem?_idxOf normalizedClauseMember
  rw [List.getElem?_map] at clauseLookup
  cases taggedLookup : taggedBends[
      (taggedBends.map (normalizedBendClauseAt source)).idxOf
        (normalizedBendClauseAt source taggedBend)]? with
  | none =>
      simp [taggedLookup] at clauseLookup
  | some selected =>
      have selectedClauseEq : normalizedBendClauseAt source selected =
          normalizedBendClauseAt source taggedBend := by
        simpa [taggedLookup] using clauseLookup
      have normalizedTaggedEq :
          (wrappedNormalizedRouteBendLink source selected.1, selected.2) =
            (wrappedNormalizedRouteBendLink source taggedBend.1,
              taggedBend.2) :=
        PeriodicEquality.normalizedClause_injective selectedClauseEq
      have portsEq := routeBend_ports_eq_of_wrappedNormalizedLink_eq
        source selected.1 taggedBend.1
          (congrArg Prod.fst normalizedTaggedEq)
      have directionEq : selected.2 = taggedBend.2 :=
        congrArg (fun tagged : PeriodicEquality.NormalizedLink
          (WrappedPeriodicPlanarSATVariable Variable) × Bool => tagged.2)
          normalizedTaggedEq
      have descriptorEq :
          normalizedBendClauseDescriptorAt source selected =
            normalizedBendClauseDescriptorAt source taggedBend := by
        unfold normalizedBendClauseDescriptorAt
        rw [metadataClauseDescriptor_bendClauseMetadataAt_eq,
          metadataClauseDescriptor_bendClauseMetadataAt_eq,
          bendLinkNextSlice_eq_false, bendLinkNextSlice_eq_false,
          portsEq.1, portsEq.2, directionEq]
      rw [List.getElem?_map, taggedLookup]
      simpa only [Option.map_some] using congrArg some descriptorEq

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
