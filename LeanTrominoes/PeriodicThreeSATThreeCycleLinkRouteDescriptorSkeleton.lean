/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterSkeleton
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterSourceInputSemantics
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAffineIndices
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationData

/-! # Target-erased skeleton of actual cycle-link descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkDescriptorStreams

theorem zipIdx_zipIdx_affine
    {Value : Type*} (values : List Value)
    (clauseStart linkStart : Nat) :
    (values.zipIdx (clauseStart + linkStart)).zipIdx linkStart =
      (values.zipIdx linkStart).map fun tagged =>
        ((tagged.1, clauseStart + tagged.2), tagged.2) := by
  induction values generalizing linkStart with
  | nil => rfl
  | cons value values induction =>
      simp only [List.zipIdx_cons, List.map_cons]
      rw [show clauseStart + linkStart + 1 =
          clauseStart + (linkStart + 1) by omega,
        induction (linkStart + 1)]

theorem map_eraseTargetData_cycleLinkIncidenceBlock
    (source : PeriodicCNF.SourceSplitRouteDescriptorTokens.Source)
    (taggedLink :
      (ThreeOccurrenceVariable Nat × ThreeOccurrenceVariable Nat) × Nat)
    (linkIndex : Nat)
    (clauseIndexEq : taggedLink.2 =
      source.formula.clauses.length + linkIndex) :
    ((cycleLinkIncidenceBlock taggedLink).zipIdx (2 * linkIndex)).map
        (fun taggedIncidence =>
          PeriodicCNF.SourceCycleLinkRouteEmitter.eraseTargetData
            (cycleLinkRouteDescriptor source.formula
              taggedIncidence.1 taggedIncidence.2)) =
      PeriodicCNF.SourceCycleLinkRouteEmitter.skeletonBlock
        (PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput source)
        linkIndex := by
  rcases taggedLink with ⟨link, clauseIndex⟩
  change clauseIndex = source.formula.clauses.length + linkIndex
    at clauseIndexEq
  subst clauseIndex
  simp [cycleLinkIncidenceBlock, cycleLinkSourceIncidence,
    cycleLinkTargetIncidence, cycleLinkRouteDescriptor,
    PeriodicCNF.SourceCycleLinkRouteEmitter.eraseTargetData,
    PeriodicCNF.SourceCycleLinkRouteEmitter.skeletonBlock,
    PeriodicCNF.SourceCycleLinkRouteEmitter.sourceSkeleton,
    PeriodicCNF.SourceCycleLinkRouteEmitter.targetSkeleton,
    PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput_literalCount,
    PeriodicCNF.clauseAnchor, implicationClause, Cell.sub]
  omega

/-- The actual descriptors and emitter descriptors agree on all fields except
the target vertex and target port rank. -/
theorem map_eraseTargetData_cycleLinkRouteDescriptors
    (source : PeriodicCNF.SourceSplitRouteDescriptorTokens.Source) :
    (cycleLinkRouteDescriptors source.formula).map
        PeriodicCNF.SourceCycleLinkRouteEmitter.eraseTargetData =
      PeriodicCNF.SourceCycleLinkRouteEmitter.skeletons
        (PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput source) := by
  let input := PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput source
  unfold cycleLinkRouteDescriptors
  rw [List.map_map, cycleLinkIncidences_zipIdx]
  have indexed := zipIdx_zipIdx_affine
    (allCycleLinks source.formula) source.formula.clauses.length 0
  simp only [Nat.add_zero] at indexed
  rw [indexed]
  simp only [List.map_flatMap, List.flatMap_map,
    Function.comp_def]
  have blocksEq :
      ((allCycleLinks source.formula).zipIdx).flatMap (fun taggedLink =>
        ((cycleLinkIncidenceBlock
          (taggedLink.1,
            source.formula.clauses.length + taggedLink.2)).zipIdx
              (2 * taggedLink.2)).map (fun taggedIncidence =>
            PeriodicCNF.SourceCycleLinkRouteEmitter.eraseTargetData
              (cycleLinkRouteDescriptor source.formula
                taggedIncidence.1 taggedIncidence.2))) =
        ((allCycleLinks source.formula).zipIdx).flatMap
          (fun taggedLink =>
            PeriodicCNF.SourceCycleLinkRouteEmitter.skeletonBlock
              input taggedLink.2) := by
    apply List.flatMap_congr
    intro taggedLink _
    exact map_eraseTargetData_cycleLinkIncidenceBlock source
      (taggedLink.1,
        source.formula.clauses.length + taggedLink.2)
      taggedLink.2 rfl
  rw [blocksEq]
  unfold PeriodicCNF.SourceCycleLinkRouteEmitter.skeletons
  have indexStream :
      (allCycleLinks source.formula).zipIdx.map Prod.snd =
        List.range (PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput
          source).literalCount := by
    rw [List.zipIdx_map_snd, List.range_eq_range',
      allCycleLinks_length,
      PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput_literalCount]
  calc
    ((allCycleLinks source.formula).zipIdx).flatMap
        (fun taggedLink =>
          PeriodicCNF.SourceCycleLinkRouteEmitter.skeletonBlock
            input taggedLink.2) =
        (((allCycleLinks source.formula).zipIdx).map Prod.snd).flatMap
          (PeriodicCNF.SourceCycleLinkRouteEmitter.skeletonBlock input) := by
      rw [List.flatMap_map]
    _ = (List.range
          (PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput
            source).literalCount).flatMap
          (PeriodicCNF.SourceCycleLinkRouteEmitter.skeletonBlock input) := by
      rw [indexStream]

end CycleLinkDescriptorStreams
end PeriodicThreeSATThree
end LeanTrominoes
