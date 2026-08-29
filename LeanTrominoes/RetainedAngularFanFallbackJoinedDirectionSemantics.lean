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

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
