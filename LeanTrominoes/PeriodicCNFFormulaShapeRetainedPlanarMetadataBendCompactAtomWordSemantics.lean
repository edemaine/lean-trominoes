/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRoutedClauseNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendRepresentativeDescriptors
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord
import LeanTrominoes.PeriodicOrthocrossingRouteBendCompactAtomWordData

/-! # Compact atom words of normalized retained-bend links -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The compact word of a normalized base bend's first endpoint is the
tagged carrier key of its incoming finish terminal. -/
theorem wrappedNormalizedRouteBendLink_first_compactAtomWord
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWord : Variable → List Bool)
    (routeBend : RouteBend)
    (translateZero : routeBend.translate = (0, 0)) :
    RetainedCompactAtomWords.word sourceWord
        (wrappedNormalizedRouteBendLink source routeBend).first =
      routeBend.incomingTerminal.compactAtomWord := by
  unfold wrappedNormalizedRouteBendLink RetainedCompactAtomWords.word
  rw [carrierWrappedNormalizeLink_first_original,
    RouteBend.normalize_equalityLink_first]
  simp [SegmentTerminal.compactAtomWord,
    RetainedCompactAtomWords.carrierPair,
    RetainedCompactAtomWords.zeroCarrierNode,
    CarrierNodeSourceKeys.pair,
    CarrierNodeSourceKeys.taggedKey,
    periodicCarrierNodeToPlanarSATVariable,
    SegmentTerminal.carrierKey,
    PeriodicGridDrawing.SegmentOccurrenceKey,
    RouteBend.incomingTerminal, translateZero]

/-- The compact word of a normalized base bend's second endpoint is the
tagged carrier key of its outgoing start terminal. -/
theorem wrappedNormalizedRouteBendLink_second_compactAtomWord
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWord : Variable → List Bool)
    (routeBend : RouteBend)
    (translateZero : routeBend.translate = (0, 0)) :
    RetainedCompactAtomWords.word sourceWord
        (wrappedNormalizedRouteBendLink source routeBend).second =
      routeBend.outgoingTerminal.compactAtomWord := by
  unfold wrappedNormalizedRouteBendLink RetainedCompactAtomWords.word
  rw [carrierWrappedNormalizeLink_second_original,
    RouteBend.normalize_equalityLink_second]
  simp [SegmentTerminal.compactAtomWord,
    RetainedCompactAtomWords.carrierPair,
    RetainedCompactAtomWords.zeroCarrierNode,
    CarrierNodeSourceKeys.pair,
    CarrierNodeSourceKeys.taggedKey,
    periodicCarrierNodeToPlanarSATVariable,
    SegmentTerminal.carrierKey,
    PeriodicGridDrawing.SegmentOccurrenceKey,
    RouteBend.outgoingTerminal, translateZero]

/-- One untranslated bend's physical four-word block is exactly the compact
atom-word block of its wrapped normalized equality link. -/
theorem routeBend_compactAtomWords_eq_normalizedLink
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWord : Variable → List Bool)
    (routeBend : RouteBend)
    (translateZero : routeBend.translate = (0, 0)) :
    routeBend.compactAtomWords =
      let link := wrappedNormalizedRouteBendLink source routeBend
      [RetainedCompactAtomWords.word sourceWord link.first,
        RetainedCompactAtomWords.word sourceWord link.second,
        RetainedCompactAtomWords.word sourceWord link.first,
        RetainedCompactAtomWords.word sourceWord link.second] := by
  dsimp only
  rw [wrappedNormalizedRouteBendLink_first_compactAtomWord
      source sourceWord routeBend translateZero,
    wrappedNormalizedRouteBendLink_second_compactAtomWord
      source sourceWord routeBend translateZero]
  rfl

/-- The complete untranslated semantic bend stream is exactly the repeated
compact endpoint-word stream of the canonical normalized bend links. -/
theorem baseRouteBends_compactAtomWords_eq_normalizedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWord : Variable → List Bool) :
    (baseRouteBends source).flatMap RouteBend.compactAtomWords =
      (baseBendNormalizedLinks source).flatMap fun link =>
        [RetainedCompactAtomWords.word sourceWord link.first,
          RetainedCompactAtomWords.word sourceWord link.second,
          RetainedCompactAtomWords.word sourceWord link.first,
          RetainedCompactAtomWords.word sourceWord link.second] := by
  rw [baseBendNormalizedLinks_eq_map_baseRouteBends,
    List.flatMap_map]
  apply List.flatMap_congr
  intro routeBend routeBendMember
  apply routeBend_compactAtomWords_eq_normalizedLink
  unfold baseRouteBends at routeBendMember
  rcases List.mem_flatMap.mp routeBendMember with
    ⟨descriptor, descriptorMember, routeBendMember⟩
  unfold routeBends at routeBendMember
  exact (routeBendsAux_member_data descriptor.edgeIndex (0, 0)
    descriptor.route 0 routeBendMember).2.1

/-- Descriptor-major form of the complete compact bend-word identity. -/
theorem numericRouteDescriptors_bendCompactAtomWords_eq_normalizedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWord : Variable → List Bool) :
    ((numericRouteDescriptors source).flatMap fun descriptor =>
      routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
        RouteBend.compactAtomWords =
      (baseBendNormalizedLinks source).flatMap fun link =>
        [RetainedCompactAtomWords.word sourceWord link.first,
          RetainedCompactAtomWords.word sourceWord link.second,
          RetainedCompactAtomWords.word sourceWord link.first,
          RetainedCompactAtomWords.word sourceWord link.second] := by
  simpa only [baseRouteBends] using
    baseRouteBends_compactAtomWords_eq_normalizedLinks source sourceWord

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
