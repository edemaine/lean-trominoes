/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCompactAtomWordData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableTargetNormalization
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord

/-! # Semantic target-terminal compact words of CNF descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing
open FormulaShapeRetainedPlanarMetadataDirection

private theorem zipIdx_getLastD_snd_of_ne_nil
    {Value : Type*} : ∀ (values : List Value) (start : Nat)
      (default : Value × Nat), values ≠ [] →
      ((values.zipIdx start).getLastD default).2 =
        start + values.length - 1 := by
  intro values
  induction values with
  | nil =>
      intro start default nonempty
      exact (nonempty rfl).elim
  | cons first rest induction =>
      intro start default _nonempty
      cases rest with
      | nil => simp
      | cons second tail =>
          change
            (((second :: tail).zipIdx (start + 1)).getLastD default).2 =
              start + (first :: second :: tail).length - 1
          rw [induction (start + 1) default (by simp)]
          simp
          omega

private theorem zipIdx_getLastD_snd_zero
    {Value : Type*} (values : List Value) (default : Value) :
    ((values.zipIdx 0).getLastD (default, 0)).2 = values.length - 1 := by
  cases values with
  | nil => rfl
  | cons first rest =>
      simpa using zipIdx_getLastD_snd_of_ne_nil
        (first :: rest) 0 (default, 0) (by simp)

/-- One numeric incidence descriptor emits exactly the compact retained-atom
word of its normalized target terminal. -/
theorem numericRouteDescriptor_targetTerminalCompactAtomWord
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (sourceWord : Variable → List Bool)
    (translate : Cell)
    (taggedIncidence : CNFIncidence Variable × Nat)
    (taggedMember :
      taggedIncidence ∈ formula.incidencesWithMetadata.zipIdx) :
    RouteDescriptorPairAffine.routeDescriptorTargetTerminalCompactAtomWord
        (taggedIncidence.1.numericRouteDescriptor
          formula taggedIncidence.2) =
      RetainedCompactAtomWords.word sourceWord
        (externalWrappedVariableNormalization formula
          (.carrier (.terminal
            ((⟨taggedIncidence.1, taggedIncidence.2, translate⟩ :
                CNFRouteOccurrence Variable).targetTerminal formula)))).1 := by
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨taggedIncidence.1, taggedIncidence.2, translate⟩
  have normalized :=
    externalWrappedVariableNormalization_targetTerminal_eq
      formula wellFormed taggedIncidence taggedMember translate
  change
    RouteDescriptorPairAffine.routeDescriptorTargetTerminalCompactAtomWord
        (taggedIncidence.1.numericRouteDescriptor
          formula taggedIncidence.2) =
      RetainedCompactAtomWords.word sourceWord
        (externalWrappedVariableNormalization formula
          (.carrier (.terminal (occurrence.targetTerminal formula)))).1
  have normalized' :
      externalWrappedVariableNormalization formula
          (.carrier (.terminal (occurrence.targetTerminal formula))) =
        (⟨PeriodicPlanarSATVariable.terminal
            (occurrence.targetTerminal formula).indexed .finish⟩,
          occurrence.variableOccurrence.2) := by
    simpa [occurrence] using normalized
  rw [normalized']
  have descriptorEq :=
    CNFIncidence.routeDescriptor_eq_numericRouteDescriptor
      formula taggedIncidence taggedMember
  simp only [RouteDescriptorPairAffine.routeDescriptorTargetTerminalCompactAtomWord,
    RetainedCompactAtomWords.word,
    RetainedCompactAtomWords.carrierPair,
    RetainedCompactAtomWords.zeroCarrierNode,
    CarrierNodeSourceKeys.pair,
    CarrierNodeSourceKeys.taggedKey,
    SegmentTerminal.carrierKey,
    CarrierNodeSourceKeys.segmentEndTag,
    PeriodicGridDrawing.SegmentOccurrenceKey,
    CNFRouteOccurrence.edge,
    CNFRouteOccurrence.targetTerminal,
    CNFRouteOccurrence.taggedSegments]
  dsimp [occurrence]
  rw [constructedEdgeRoute_eq_descriptorRoute, descriptorEq]
  unfold defaultTaggedGridSegment
  rw [zipIdx_getLastD_snd_zero]
  rfl

end PeriodicCNF
end LeanTrominoes
