/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalPointBlockNodup

/-! # Membership semantics of one canonical point block -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- A filtered point-grid block contains precisely its computed oriented
intersection, exactly when the occurrence-pair predicate accepts. -/
theorem mem_canonicalOrientedPointBlock_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (record : CrossingRecord) :
    record ∈ canonicalOrientedPointBlock graph pair ↔
      record = orientedCrossingCandidate graph pair.1 pair.2 ∧
        canonicalOrientedOccurrencePair graph pair = true := by
  let candidate := orientedCrossingCandidate graph pair.1 pair.2
  constructor
  · intro recordMember
    rcases List.mem_filter.mp recordMember with
      ⟨recordMember, horizontalValue⟩
    rcases List.mem_filter.mp recordMember with
      ⟨recordMember, canonicalValue⟩
    rcases List.mem_map.mp recordMember with
      ⟨point, _pointMember, recordEq⟩
    have canonical :
        (occurrencePairCrossingAtPoint pair point).IsCanonical graph := by
      rw [recordEq]
      exact of_decide_eq_true canonicalValue
    have horizontal :
        GridSegment.IsHorizontal
          ((occurrencePairCrossingAtPoint pair point).firstSegment graph) := by
      rw [recordEq]
      exact of_decide_eq_true horizontalValue
    have vertical :
        GridSegment.IsVertical
          ((occurrencePairCrossingAtPoint pair point).secondSegment graph) := by
      rcases canonical.2.2.2.2 with
        horizontalVertical | verticalHorizontal
      · exact horizontalVertical.2
      · exact False.elim (verticalHorizontal.1.2 horizontal.1)
    have intersectionEq :
        orientedIntersectionPoint
            ((occurrencePairCrossingAtPoint pair point).firstSegment graph)
            ((occurrencePairCrossingAtPoint pair point).secondSegment graph) =
          point :=
      orientedIntersectionPoint_eq horizontal vertical
        canonical.2.2.1 canonical.2.2.2.1
    have pointRecordEq :
        occurrencePairCrossingAtPoint pair point = candidate := by
      unfold candidate occurrencePairCrossingAtPoint
        orientedCrossingCandidate
      congr
      simpa [occurrencePairCrossingAtPoint,
        CrossingRecord.firstSegment,
        CrossingRecord.secondSegment] using intersectionEq.symm
    have candidateData :
        candidate.IsCanonical graph ∧
          (candidate.firstSegment graph).IsHorizontal := by
      rw [← pointRecordEq]
      exact ⟨canonical, horizontal⟩
    refine ⟨recordEq.symm.trans pointRecordEq, ?_⟩
    unfold canonicalOrientedOccurrencePair
    exact decide_eq_true candidateData
  · rintro ⟨rfl, accepted⟩
    have acceptedData :
        candidate.IsCanonical graph ∧
          (candidate.firstSegment graph).IsHorizontal := by
      simpa [canonicalOrientedOccurrencePair, candidate] using
        (of_decide_eq_true accepted)
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨?_,
      decide_eq_true acceptedData.1⟩,
      decide_eq_true acceptedData.2⟩
    apply List.mem_map.mpr
    refine ⟨candidate.point,
      (mem_fundamentalPoints_iff graph candidate.point).mpr
        acceptedData.1.1, ?_⟩
    unfold candidate occurrencePairCrossingAtPoint
      orientedCrossingCandidate
    rfl

end LeanTrominoes.PeriodicOrthocrossing
