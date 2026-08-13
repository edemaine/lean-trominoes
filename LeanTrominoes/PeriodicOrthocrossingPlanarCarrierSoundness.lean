/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarRouteCore

/-!
# Soundness of complete straight-segment carriers

The route core omits an explicit equality link between the two boundary
variables at one crossover site because the crossover gadget itself enforces
that equality.  This file combines those internal crossover laws with the
links between consecutive sites, proving that every node on one complete
straight segment carrier has one common value.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Pairwise equality of assignment images makes the images of every two
members equal, regardless of their order in the list. -/
theorem assignment_eq_of_pairwise
    {Node : Type*}
    (assignment : Node → Bool) (nodes : List Node)
    (pairwise :
      nodes.Pairwise fun first second =>
        assignment first = assignment second) :
    ∀ first ∈ nodes, ∀ second ∈ nodes,
      assignment first = assignment second := by
  intro first firstMem second secondMem
  induction nodes with
  | nil =>
      simp at firstMem
  | cons head tail induction =>
      rw [List.pairwise_cons] at pairwise
      simp only [List.mem_cons] at firstMem secondMem
      rcases firstMem with firstEq | firstMem
      · subst first
        rcases secondMem with secondEq | secondMem
        · subst second
          rfl
        · exact pairwise.1 second secondMem
      · rcases secondMem with secondEq | secondMem
        · subst second
          exact (pairwise.1 first firstMem).symm
        · exact induction pairwise.2 firstMem secondMem

/-- Adjacent equalities make the images of every two members of a list
equal. -/
theorem assignment_eq_of_consecutivePairs
    {Node : Type*}
    (assignment : Node → Bool) (nodes : List Node)
    (adjacent :
      ∀ pair ∈ consecutivePairs nodes,
        assignment pair.1 = assignment pair.2) :
    ∀ first ∈ nodes, ∀ second ∈ nodes,
      assignment first = assignment second := by
  have chain :
      nodes.IsChain fun first second =>
        assignment first = assignment second := by
    induction nodes with
    | nil =>
        exact .nil
    | cons first rest induction =>
        cases rest with
        | nil =>
            exact .singleton first
        | cons second rest =>
            rw [List.isChain_cons_cons]
            constructor
            · exact adjacent (first, second) (by simp [consecutivePairs])
            · apply induction
              intro pair pairMem
              exact adjacent pair (by
                simp only [consecutivePairs, List.mem_cons]
                exact Or.inr pairMem)
  exact assignment_eq_of_pairwise
    assignment nodes chain.pairwise

/-- A boundary listed in the finite drawing comes from a listed canonical
crossover site. -/
theorem CrossingBoundary.crossing_mem_orientedCrossings
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {boundary : CrossingBoundary}
    (boundaryMem :
      boundary ∈ drawingCrossingBoundaries graph) :
    boundary.crossing ∈ orientedCrossingHalo graph := by
  rcases List.mem_flatMap.mp boundaryMem with
    ⟨crossing, crossingMem, boundaryMem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at boundaryMem
  rcases boundaryMem with
    boundaryEq | boundaryEq | boundaryEq | boundaryEq <;>
      subst boundary <;>
      exact orientedCrossings_subset_orientedCrossingHalo
        graph crossingMem

/-- At one canonical crossover, two boundary nodes on the same segment
carrier have equal values. -/
theorem crossingBoundary_assignment_eq_of_common_carrier
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool)
    (crossingLaws :
      ∀ crossing ∈ orientedCrossingHalo graph,
        assignment
            (.inl (.boundary ⟨crossing, .left⟩)) =
            assignment
              (.inl (.boundary ⟨crossing, .right⟩)) ∧
          assignment
              (.inl (.boundary ⟨crossing, .top⟩)) =
            assignment
              (.inl (.boundary ⟨crossing, .bottom⟩)))
    (crossing : CrossingRecord)
    (crossingMem : crossing ∈ orientedCrossingHalo graph)
    (firstSide secondSide : CrossingSide)
    (commonCarrier :
      (CrossingBoundary.mk crossing firstSide).carrierKey =
        (CrossingBoundary.mk crossing secondSide).carrierKey) :
    assignment
        (.inl (.boundary ⟨crossing, firstSide⟩)) =
      assignment
        (.inl (.boundary ⟨crossing, secondSide⟩)) := by
  have laws := crossingLaws crossing crossingMem
  have different :=
    (orientedCrossingHalo_sound graph crossingMem).2.2.2.2.1
  cases firstSide <;> cases secondSide <;>
    simp only [CrossingBoundary.carrierKey] at commonCarrier
  · rfl
  · exact laws.1
  · exact (different commonCarrier).elim
  · exact (different commonCarrier).elim
  · exact laws.1.symm
  · rfl
  · exact (different commonCarrier).elim
  · exact (different commonCarrier).elim
  · exact (different commonCarrier.symm).elim
  · exact (different commonCarrier.symm).elim
  · rfl
  · exact laws.2
  · exact (different commonCarrier.symm).elim
  · exact (different commonCarrier.symm).elim
  · exact laws.2.symm
  · rfl

/-- Every consecutive pair in a complete carrier chain has equal values:
either it is an explicit equality link or it is the internal pair of one
crossover gadget. -/
theorem completeCarrierConsecutivePair_assignment_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool)
    (crossingLaws :
      ∀ crossing ∈ orientedCrossingHalo graph,
        assignment
            (.inl (.boundary ⟨crossing, .left⟩)) =
            assignment
              (.inl (.boundary ⟨crossing, .right⟩)) ∧
          assignment
              (.inl (.boundary ⟨crossing, .top⟩)) =
            assignment
              (.inl (.boundary ⟨crossing, .bottom⟩)))
    (carrierLaws :
      ∀ link ∈ drawingCompleteCarrierLinks graph,
        assignment (.inl link.first) =
          assignment (.inl link.second))
    (key : Nat × Nat × Cell)
    (pair : CarrierNode × CarrierNode)
    (pairMem :
      pair ∈ consecutivePairs
        (completeCarrierNodes graph key)) :
    assignment (.inl pair.1) =
      assignment (.inl pair.2) := by
  have members := mem_of_mem_consecutivePairs pairMem
  have firstData :=
    (mem_completeCarrierNodes_iff graph key pair.1).mp members.1
  have secondData :=
    (mem_completeCarrierNodes_iff graph key pair.2).mp members.2
  by_cases sameSite : pair.1.sameCrossoverSite pair.2
  · rcases pair with ⟨first, second⟩
    cases first with
    | terminal firstTerminal =>
        simp [CarrierNode.sameCrossoverSite] at sameSite
    | boundary firstBoundary =>
        cases second with
        | terminal secondTerminal =>
            simp [CarrierNode.sameCrossoverSite] at sameSite
        | boundary secondBoundary =>
            rcases firstBoundary with ⟨firstCrossing, firstSide⟩
            rcases secondBoundary with ⟨secondCrossing, secondSide⟩
            have crossingEq : firstCrossing = secondCrossing := by
              simpa [CarrierNode.sameCrossoverSite] using sameSite
            subst secondCrossing
            have boundaryMem :
                (CrossingBoundary.mk firstCrossing firstSide) ∈
                  drawingCrossingBoundaries graph := by
              simpa [drawingCarrierNodes] using firstData.1
            exact
              crossingBoundary_assignment_eq_of_common_carrier
                graph assignment crossingLaws firstCrossing
                (CrossingBoundary.crossing_mem_orientedCrossings
                  graph boundaryMem)
                firstSide secondSide
                (firstData.2.trans secondData.2.symm)
  · have keyMem :
        key ∈ drawingCompleteCarrierKeys graph := by
      simp only [drawingCompleteCarrierKeys, List.mem_dedup,
        List.mem_map]
      exact ⟨pair.1, firstData.1, firstData.2⟩
    have localLinkMem :
        carrierNodePairLink graph pair ∈
          completeCarrierLinks graph key := by
      apply List.mem_map.mpr
      refine ⟨pair, ?_, rfl⟩
      exact List.mem_filter.mpr
        ⟨pairMem, by simp [sameSite]⟩
    exact carrierLaws (carrierNodePairLink graph pair)
      (List.mem_flatMap.mpr
        ⟨key, keyMem, localLinkMem⟩)

/-- Every two nodes on one complete straight-segment carrier receive the
same value under the crossover and carrier-link laws. -/
theorem completeCarrierNodes_assignment_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool)
    (crossingLaws :
      ∀ crossing ∈ orientedCrossingHalo graph,
        assignment
            (.inl (.boundary ⟨crossing, .left⟩)) =
            assignment
              (.inl (.boundary ⟨crossing, .right⟩)) ∧
          assignment
              (.inl (.boundary ⟨crossing, .top⟩)) =
            assignment
              (.inl (.boundary ⟨crossing, .bottom⟩)))
    (carrierLaws :
      ∀ link ∈ drawingCompleteCarrierLinks graph,
        assignment (.inl link.first) =
          assignment (.inl link.second))
    (key : Nat × Nat × Cell)
    {first second : CarrierNode}
    (firstMem : first ∈ completeCarrierNodes graph key)
    (secondMem : second ∈ completeCarrierNodes graph key) :
    assignment (.inl first) = assignment (.inl second) := by
  exact
    assignment_eq_of_consecutivePairs
      (assignment ∘ Sum.inl)
      (completeCarrierNodes graph key)
      (completeCarrierConsecutivePair_assignment_eq
        graph assignment crossingLaws carrierLaws key)
      first firstMem second secondMem

/-- The start and finish terminals of every listed neighboring straight
segment occurrence carry the same value. -/
theorem segmentOccurrenceTerminals_assignment_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool)
    (crossingLaws :
      ∀ crossing ∈ orientedCrossingHalo graph,
        assignment
            (.inl (.boundary ⟨crossing, .left⟩)) =
            assignment
              (.inl (.boundary ⟨crossing, .right⟩)) ∧
          assignment
              (.inl (.boundary ⟨crossing, .top⟩)) =
            assignment
              (.inl (.boundary ⟨crossing, .bottom⟩)))
    (carrierLaws :
      ∀ link ∈ drawingCompleteCarrierLinks graph,
        assignment (.inl link.first) =
          assignment (.inl link.second))
    (indexed : IndexedGridSegment)
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (translate : Cell)
    (translateNeighbor : IsNeighborTranslation translate) :
    assignment
        (.inl (.terminal ⟨indexed, translate, .start⟩)) =
      assignment
        (.inl (.terminal ⟨indexed, translate, .finish⟩)) := by
  let startTerminal : SegmentTerminal :=
    ⟨indexed, translate, .start⟩
  let finishTerminal : SegmentTerminal :=
    ⟨indexed, translate, .finish⟩
  have occurrenceMem :
      (indexed, translate) ∈ neighborOccurrences graph :=
    (mem_neighborOccurrences_iff graph _).mpr
      ⟨indexedMem, translateNeighbor⟩
  have startTerminalMem :
      startTerminal ∈ drawingSegmentTerminals graph := by
    apply List.mem_flatMap.mpr
    refine ⟨(indexed, translate), occurrenceMem, ?_⟩
    simp [occurrenceTerminals, startTerminal]
  have finishTerminalMem :
      finishTerminal ∈ drawingSegmentTerminals graph := by
    apply List.mem_flatMap.mpr
    refine ⟨(indexed, translate), occurrenceMem, ?_⟩
    simp [occurrenceTerminals, finishTerminal]
  have startNodeMem :
      CarrierNode.terminal startTerminal ∈
        completeCarrierNodes graph startTerminal.carrierKey := by
    apply (mem_completeCarrierNodes_iff
      graph startTerminal.carrierKey _).mpr
    constructor
    · apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨startTerminal, startTerminalMem, rfl⟩
    · rfl
  have finishNodeMem :
      CarrierNode.terminal finishTerminal ∈
        completeCarrierNodes graph startTerminal.carrierKey := by
    apply (mem_completeCarrierNodes_iff
      graph startTerminal.carrierKey _).mpr
    constructor
    · apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨finishTerminal, finishTerminalMem, rfl⟩
    · rfl
  exact completeCarrierNodes_assignment_eq
    graph assignment crossingLaws carrierLaws
    startTerminal.carrierKey startNodeMem finishNodeMem

end PeriodicOrthocrossing
end LeanTrominoes
