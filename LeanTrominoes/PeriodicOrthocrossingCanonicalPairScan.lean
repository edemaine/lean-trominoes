/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingHalo

/-! # Quadratic pair scan for canonical oriented crossings -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Scan ordered neighboring segment-occurrence pairs at their unique
oriented intersection point, retaining just canonical horizontal-first
crossings. -/
def orientedCrossingPairScan
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingRecord :=
  (((crossingHaloCandidates graph).filter fun record =>
      record.IsCanonical graph).filter fun record =>
        (record.firstSegment graph).IsHorizontal).dedup

/-- The quadratic pair scan and the original point-grid enumeration contain
exactly the same canonical oriented crossing records. -/
@[simp] theorem mem_orientedCrossingPairScan_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    record ∈ orientedCrossingPairScan graph ↔
      record ∈ orientedCrossings graph := by
  constructor
  · intro pairMember
    rw [orientedCrossingPairScan, List.mem_dedup,
      List.mem_filter, List.mem_filter] at pairMember
    have pairData :=
      (mem_crossingHaloCandidates_iff graph record).mp
        pairMember.1.1
    have canonical : record.IsCanonical graph :=
      of_decide_eq_true pairMember.1.2
    have horizontal : (record.firstSegment graph).IsHorizontal :=
      of_decide_eq_true pairMember.2
    apply (mem_orientedCrossings_iff graph record).mpr
    refine ⟨?_, horizontal⟩
    rw [canonicalCrossings, List.mem_filter]
    refine ⟨?_, decide_eq_true canonical⟩
    have firstData :=
      (mem_neighborOccurrences_iff graph _).mp pairData.1
    have secondData :=
      (mem_neighborOccurrences_iff graph _).mp pairData.2.1
    exact mem_crossingCandidates graph
      firstData.1 secondData.1 firstData.2 secondData.2 canonical.1
  · intro orientedMember
    have sound := orientedCrossings_sound graph orientedMember
    have canonical := sound.2.2.2.2.1
    have pointEq :
        record.point = orientedIntersectionPoint
          (record.firstSegment graph) (record.secondSegment graph) :=
      (orientedIntersectionPoint_eq
        sound.2.2.2.2.2.1 sound.2.2.2.2.2.2
        canonical.2.2.1 canonical.2.2.2.1).symm
    have pairMember : record ∈ crossingHaloCandidates graph :=
      (mem_crossingHaloCandidates_iff graph record).mpr
        ⟨(mem_neighborOccurrences_iff graph _).mpr
            ⟨sound.1, sound.2.2.1⟩,
          (mem_neighborOccurrences_iff graph _).mpr
            ⟨sound.2.1, sound.2.2.2.1⟩,
          pointEq⟩
    rw [orientedCrossingPairScan, List.mem_dedup,
      List.mem_filter, List.mem_filter]
    exact ⟨⟨pairMember, decide_eq_true canonical⟩,
      decide_eq_true sound.2.2.2.2.2.1⟩

/-- In particular, the pair scan computes the exact number of canonical
oriented crossings without enumerating every point of the drawing square. -/
theorem orientedCrossingPairScan_length_eq_orientedCrossings
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (orientedCrossingPairScan graph).length =
      (orientedCrossings graph).length := by
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_dedup _) (orientedCrossings_nodup graph)).mpr
  intro record
  exact mem_orientedCrossingPairScan_iff graph record

end PeriodicOrthocrossing
end LeanTrominoes
