/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteOrthocrossingBounds
import LeanTrominoes.PeriodicOrthocrossingCrossingNormalization
import LeanTrominoes.PeriodicOrthocrossingCarrierOrbitOwnership

/-! # Canonical crossings of finite zero-offset graphs stay in one copy -/
namespace LeanTrominoes.PeriodicOrthocrossing

theorem canonicalCrossings_translates_zero
    {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (degree : graph.DegreeAtMost 3)
    (zero : ∀ edge∈graph.edges, edge.offset=(0,0))
    {record : CrossingRecord} (member : record∈canonicalCrossings graph) :
    record.firstTranslate=(0,0) ∧ record.secondTranslate=(0,0) := by
  have sound := canonicalCrossings_sound graph member
  have canonical := sound.2.2.2.2
  exact ⟨drawing_occurrence_translate_zero wellFormed degree zero sound.1 canonical.1
      canonical.2.2.1,
    drawing_occurrence_translate_zero wellFormed degree zero sound.2.1 canonical.1
      canonical.2.2.2.1⟩

theorem zeroOffsetGraph_isLocal {Vertex : Type*} (graph : PeriodicGraph Vertex)
    (zero : ∀ edge∈graph.edges, edge.offset=(0,0)) : graph.IsLocal := by
  intro edge member
  simp [PeriodicEdge.span,zero edge member]

theorem crossingHalo_translates_eq_periodShift
    {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (degree : graph.DegreeAtMost 3)
    (zero : ∀ edge∈graph.edges, edge.offset=(0,0))
    {record : CrossingRecord} (member : record∈orientedCrossingHalo graph) :
    record.firstTranslate=crossingPeriodShift graph record ∧
      record.secondTranslate=crossingPeriodShift graph record := by
  have normalized := periodNormalize_mem_orientedCrossings wellFormed degree
    (zeroOffsetGraph_isLocal graph zero) member
  have canonical := (mem_orientedCrossings_iff graph _).mp normalized |>.1
  have offsets := canonicalCrossings_translates_zero wellFormed degree zero canonical
  have first := periodNormalize_firstTranslate_add_shift graph record
  have second := periodNormalize_secondTranslate_add_shift graph record
  rw [offsets.1] at first
  rw [offsets.2] at second
  exact ⟨by simpa [Cell.add] using first.symm,by simpa [Cell.add] using second.symm⟩

theorem retainedCrossings_translates_eq_periodShift
    {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (degree : graph.DegreeAtMost 3)
    (zero : ∀ edge∈graph.edges, edge.offset=(0,0))
    {record : CrossingRecord} (member : record∈retainedCrossings graph) :
    record.firstTranslate=crossingPeriodShift graph record ∧
      record.secondTranslate=crossingPeriodShift graph record := by
  obtain ⟨canonical,canonicalMember,translated⟩ := List.mem_flatMap.mp member
  obtain ⟨shift,_,recordEq⟩ := List.mem_map.mp translated
  subst record
  have canonicalMem := (mem_orientedCrossings_iff graph _).mp canonicalMember |>.1
  have offsets := canonicalCrossings_translates_zero wellFormed degree zero canonicalMem
  have fundamental := (canonicalCrossings_sound graph canonicalMem).2.2.2.2.1
  rw [crossingPeriodShift_periodTranslate,
    crossingPeriodShift_eq_zero_of_inFundamental graph canonical fundamental]
  simp [CrossingRecord.periodTranslate,offsets.1,offsets.2,Cell.add]

end LeanTrominoes.PeriodicOrthocrossing
