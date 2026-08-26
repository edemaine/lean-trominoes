/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNormalizedLinkData
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorBendNodup
import LeanTrominoes.PeriodicCNFPlanarOccurrences
import LeanTrominoes.PeriodicOrthocrossingBendNormalizationDegree

/-! # Geometry of canonical normalized retained-bend links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Wrapped normalization erases the common translated occurrence of a
routed bend, just as ordinary carrier normalization does. -/
theorem wrappedNormalizedRouteBendLink_eq_eraseTranslation
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (routeBend : RouteBend) :
    wrappedNormalizedRouteBendLink source routeBend =
      wrappedNormalizedRouteBendLink source
        routeBend.eraseTranslation := by
  unfold wrappedNormalizedRouteBendLink
  apply (carrierWrappedNormalizeLink_eq_iff source _ _).mpr
  exact routeBend.normalize_equalityLink_eq_eraseTranslation
    source.incidenceGraph

/-- At a fixed route and segment position, changing the translated occurrence
does not change the wrapped normalized link sequence. -/
theorem routeBendsAux_wrappedNormalizedLinks_translate
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeIndex incomingSegmentIndex : Nat)
    (firstTranslate secondTranslate : Cell) :
    ∀ points : List Cell,
      (routeBendsAux routeIndex firstTranslate
          incomingSegmentIndex points).map
          (wrappedNormalizedRouteBendLink source) =
        (routeBendsAux routeIndex secondTranslate
          incomingSegmentIndex points).map
          (wrappedNormalizedRouteBendLink source) := by
  intro points
  induction points generalizing incomingSegmentIndex with
  | nil => rfl
  | cons first rest induction =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              simp only [routeBendsAux, List.map_cons]
              congr 1
              · have firstErase :=
                  wrappedNormalizedRouteBendLink_eq_eraseTranslation
                    source
                    { routeIndex := routeIndex
                      incomingSegmentIndex := incomingSegmentIndex
                      translate := firstTranslate
                      incomingStart := first
                      bend := second
                      outgoingFinish := third }
                have secondErase :=
                  wrappedNormalizedRouteBendLink_eq_eraseTranslation
                    source
                    { routeIndex := routeIndex
                      incomingSegmentIndex := incomingSegmentIndex
                      translate := secondTranslate
                      incomingStart := first
                      bend := second
                      outgoingFinish := third }
                simpa [RouteBend.eraseTranslation] using
                  firstErase.trans secondErase.symm
              · exact induction (incomingSegmentIndex + 1)

/-- Public route-level translation invariance of wrapped normalized bend
links. -/
theorem translatedRouteBendNormalizedLinks_eq_base
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (descriptor : RouteDescriptor)
    (translate : Cell) :
    translatedRouteBendNormalizedLinks source descriptor translate =
      translatedRouteBendNormalizedLinks source descriptor (0, 0) := by
  unfold translatedRouteBendNormalizedLinks routeBends
  exact routeBendsAux_wrappedNormalizedLinks_translate
    source descriptor.edgeIndex 0 translate (0, 0) descriptor.route

/-- One translated route's normalized bend links are duplicate-free. -/
theorem translatedRouteBendNormalizedLinks_nodup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (descriptor : RouteDescriptor)
    (translate : Cell) :
    (translatedRouteBendNormalizedLinks
      source descriptor translate).Nodup := by
  unfold translatedRouteBendNormalizedLinks
  apply (routeBends_nodup
    descriptor.edgeIndex translate descriptor.route).map_on
  intro first firstMember second secondMember wrappedEq
  have rawEq := (carrierWrappedNormalizeLink_eq_iff source
    (first.equalityLink source.incidenceGraph)
    (second.equalityLink source.incidenceGraph)).mp wrappedEq
  have firstEndpointEq := congrArg
    PeriodicEquality.NormalizedLink.first rawEq
  simp only [RouteBend.normalize_equalityLink_first]
    at firstEndpointEq
  have indexedEq :
      first.incomingTerminal.indexed =
        second.incomingTerminal.indexed :=
    (PeriodicCarrierNode.terminal.inj firstEndpointEq).1
  have indexEq :
      first.incomingSegmentIndex =
        second.incomingSegmentIndex :=
    congrArg IndexedGridSegment.segmentIndex indexedEq
  unfold routeBends at firstMember secondMember
  exact routeBendsAux_eq_of_index_eq
    descriptor.edgeIndex translate descriptor.route 0
    firstMember secondMember indexEq

/-- Numeric routes with distinct stored edge indices have disjoint normalized
bend-link blocks, at any translated occurrences. -/
theorem translatedRouteBendNormalizedLinks_disjoint_of_edgeIndex_ne
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (first second : RouteDescriptor)
    (edgeIndexNe : first.edgeIndex ≠ second.edgeIndex)
    (firstTranslate secondTranslate : Cell) :
    List.Disjoint
      (translatedRouteBendNormalizedLinks
        source first firstTranslate)
      (translatedRouteBendNormalizedLinks
        source second secondTranslate) := by
  rw [List.disjoint_left]
  intro link firstMember secondMember
  rcases List.mem_map.mp firstMember with
    ⟨firstBend, firstBendMember, firstEq⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondBend, secondBendMember, secondEq⟩
  have wrappedEq :
      wrappedNormalizedRouteBendLink source firstBend =
        wrappedNormalizedRouteBendLink source secondBend :=
    firstEq.trans secondEq.symm
  have rawEq := (carrierWrappedNormalizeLink_eq_iff source
    (firstBend.equalityLink source.incidenceGraph)
    (secondBend.equalityLink source.incidenceGraph)).mp wrappedEq
  have firstEndpointEq := congrArg
    PeriodicEquality.NormalizedLink.first rawEq
  simp only [RouteBend.normalize_equalityLink_first]
    at firstEndpointEq
  have indexedEq :
      firstBend.incomingTerminal.indexed =
        secondBend.incomingTerminal.indexed :=
    (PeriodicCarrierNode.terminal.inj firstEndpointEq).1
  have routeEq : firstBend.routeIndex = secondBend.routeIndex :=
    congrArg IndexedGridSegment.routeIndex indexedEq
  unfold routeBends at firstBendMember secondBendMember
  have firstData := routeBendsAux_member_data
    first.edgeIndex firstTranslate first.route 0 firstBendMember
  have secondData := routeBendsAux_member_data
    second.edgeIndex secondTranslate second.route 0 secondBendMember
  exact edgeIndexNe
    (firstData.1.symm.trans (routeEq.trans secondData.1))

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
