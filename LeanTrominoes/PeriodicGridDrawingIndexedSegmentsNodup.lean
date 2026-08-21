/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawing

/-! # Duplicate-free indexed drawing segments -/

namespace LeanTrominoes.PeriodicGridDrawing

/-- Route and within-route presentation indices make the flattened indexed
segment enumeration duplicate-free, even when geometric segments repeat. -/
theorem indexedSegments_nodup (source : PeriodicGridDrawing) :
    source.indexedSegments.Nodup := by
  have routeIndicesPairwise :
      source.edgeRoutes.zipIdx.Pairwise
        (fun first second => first.2 ≠ second.2) := by
    rw [← List.pairwise_map]
    exact List.nodup_zipIdx_map_snd source.edgeRoutes
  rw [indexedSegments, List.nodup_flatMap]
  constructor
  · intro taggedRoute _
    have taggedSegmentsNodup :
        (gridPolylineSegments taggedRoute.1).zipIdx.Nodup :=
      (List.nodup_zipIdx_map_snd
        (gridPolylineSegments taggedRoute.1)).of_map Prod.snd
    apply taggedSegmentsNodup.map_on
    intro first firstMem second secondMem equal
    have indexEqual : first.2 = second.2 :=
      congrArg IndexedGridSegment.segmentIndex equal
    have firstLookup :=
      (List.mem_zipIdx_iff_getElem?).mp firstMem
    have secondLookup :=
      (List.mem_zipIdx_iff_getElem?).mp secondMem
    have valueEqual : first.1 = second.1 := by
      rw [indexEqual] at firstLookup
      exact Option.some.inj (firstLookup.symm.trans secondLookup)
    exact Prod.ext valueEqual indexEqual
  · exact routeIndicesPairwise.imp fun
      {first second} routeIndexNe => by
        change List.Disjoint _ _
        rw [List.disjoint_left]
        intro indexed firstMember secondMember
        rcases List.mem_map.mp firstMember with
          ⟨firstSegment, _, firstEqual⟩
        rcases List.mem_map.mp secondMember with
          ⟨secondSegment, _, secondEqual⟩
        exact routeIndexNe
          (congrArg IndexedGridSegment.routeIndex
            (firstEqual.trans secondEqual.symm))

end LeanTrominoes.PeriodicGridDrawing
