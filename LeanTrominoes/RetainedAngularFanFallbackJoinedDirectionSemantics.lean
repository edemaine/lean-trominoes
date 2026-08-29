/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinSemantics
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionBatchSemantics

/-! # Joined direction words of retained fallback routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open PeriodicOrthocrossing

/-- Geometric retained-fan suffix represented by one compact query. -/
def Batch.Query.geometricSuffixDirections (query : Batch.Query) :
    List AxisDirection :=
  retainedFallbackFanSuffixDirections query.kind
    (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
      (query.direction, query.rawLength))
    query.slot

/-- Complete route-delimited words obtained by adjoining each source prefix
to the geometric retained-fan suffix represented by its aligned query. -/
def retainedJoinedDirections
    (entries : List (List AxisDirection × Batch.Query)) :
    List OutputToken :=
  entries.flatMap fun entry =>
    DelimitedRouteJoin.delimited
      (entry.1 ++ entry.2.geometricSuffixDirections)

/-- On positive query lengths, the verified stream joiner concatenates every
aligned source-prefix word with its exact geometric retained-fan suffix. -/
theorem joined_prefixes_directions_eq
    (entries : List (List AxisDirection × Batch.Query))
    (lengthPositive : ∀ entry ∈ entries, 0 < entry.2.rawLength) :
    DelimitedRouteJoin.joined
        (entries.flatMap fun entry =>
          DelimitedRouteJoin.delimited entry.1)
        (Batch.directions (entries.map Prod.snd)) =
      retainedJoinedDirections entries := by
  rw [Batch.directions_eq_retainedDirections]
  · unfold retainedJoinedDirections Batch.retainedDirections
      Batch.Query.geometricSuffixDirections
    simpa [List.flatMap_map, DelimitedRouteJoin.delimited,
      directionTokens, Batch.Query.geometricSuffixDirections,
      Function.comp_def] using
      (DelimitedRouteJoin.joined_flatMap_delimited
        (entries.map fun entry =>
          (entry.1, entry.2.geometricSuffixDirections)))
  · intro query queryMember
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp queryMember
    exact lengthPositive entry entryMember

/-- Equal-length prefix and query lists can be paired positionally before
applying the geometric join semantics. -/
theorem joined_prefixWords_directions_eq
    (prefixes : List (List AxisDirection))
    (queries : List Batch.Query)
    (lengthEq : prefixes.length = queries.length)
    (lengthPositive : ∀ query ∈ queries, 0 < query.rawLength) :
    DelimitedRouteJoin.joined
        (prefixes.flatMap DelimitedRouteJoin.delimited)
        (Batch.directions queries) =
      retainedJoinedDirections (prefixes.zip queries) := by
  have firstProjection :
      (prefixes.zip queries).map Prod.fst = prefixes :=
    List.map_fst_zip (le_of_eq lengthEq)
  have secondProjection :
      (prefixes.zip queries).map Prod.snd = queries :=
    List.map_snd_zip (le_of_eq lengthEq.symm)
  have pairedPositive :
      ∀ entry ∈ prefixes.zip queries, 0 < entry.2.rawLength := by
    intro entry entryMember
    apply lengthPositive entry.2
    have member : entry.2 ∈ (prefixes.zip queries).map Prod.snd :=
      List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    simpa only [secondProjection] using member
  have prefixProjection :
      (prefixes.zip queries).flatMap
          (fun entry => DelimitedRouteJoin.delimited entry.1) =
        prefixes.flatMap DelimitedRouteJoin.delimited := by
    rw [← List.flatMap_map, firstProjection]
  have joined := joined_prefixes_directions_eq
    (prefixes.zip queries) pairedPositive
  rw [prefixProjection, secondProjection] at joined
  exact joined

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
