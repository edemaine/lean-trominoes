/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinSemantics
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixDirectionBatchSemantics

/-! # Joined direction words of normalized ordinary fallback routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace NormalizedFallbackSuffixDirectionCompiler

open PeriodicOrthocrossing
open FallbackSuffixDirectionCompiler

/-- Canonical normalized ordinary retained-fan suffix represented by one
compact query. -/
def Batch.Query.normalizedOrdinarySuffixDirections
    (query : Batch.Query) : List AxisDirection :=
  retainedNormalizedFallbackFanSuffixDirections .ordinary
    (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
      (query.direction, query.rawLength))
    query.slot

/-- Complete route-delimited words obtained by adjoining each source prefix
to its canonical normalized ordinary suffix. -/
def retainedOrdinaryJoinedDirections
    (entries : List (List AxisDirection × Batch.Query)) :
    List OutputToken :=
  entries.flatMap fun entry =>
    DelimitedRouteJoin.delimited
      (entry.1 ++ entry.2.normalizedOrdinarySuffixDirections)

/-- The verified stream joiner concatenates every aligned source-prefix
word with its normalized ordinary suffix. -/
theorem joined_prefixes_directions_eq
    (entries : List (List AxisDirection × Batch.Query))
    (ordinary : ∀ entry ∈ entries, entry.2.kind = .ordinary)
    (lengthPositive : ∀ entry ∈ entries, 0 < entry.2.rawLength) :
    DelimitedRouteJoin.joined
        (entries.flatMap fun entry =>
          DelimitedRouteJoin.delimited entry.1)
        (Batch.directions (entries.map Prod.snd)) =
      retainedOrdinaryJoinedDirections entries := by
  rw [Batch.directions_eq_retainedOrdinaryDirections]
  · unfold retainedOrdinaryJoinedDirections
      Batch.retainedOrdinaryDirections
      Batch.Query.normalizedOrdinarySuffixDirections
    simpa [List.flatMap_map, DelimitedRouteJoin.delimited,
      directionTokens, Batch.Query.normalizedOrdinarySuffixDirections,
      Function.comp_def] using
      (DelimitedRouteJoin.joined_flatMap_delimited
        (entries.map fun entry =>
          (entry.1, entry.2.normalizedOrdinarySuffixDirections)))
  · intro query queryMember
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp queryMember
    exact ordinary entry entryMember
  · intro query queryMember
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp queryMember
    exact lengthPositive entry entryMember

/-- Equal-length prefix and ordinary-query lists can be paired positionally
before applying normalized join semantics. -/
theorem joined_prefixWords_directions_eq
    (prefixes : List (List AxisDirection))
    (queries : List Batch.Query)
    (lengthEq : prefixes.length = queries.length)
    (ordinary : ∀ query ∈ queries, query.kind = .ordinary)
    (lengthPositive : ∀ query ∈ queries, 0 < query.rawLength) :
    DelimitedRouteJoin.joined
        (prefixes.flatMap DelimitedRouteJoin.delimited)
        (Batch.directions queries) =
      retainedOrdinaryJoinedDirections (prefixes.zip queries) := by
  have firstProjection :
      (prefixes.zip queries).map Prod.fst = prefixes :=
    List.map_fst_zip (le_of_eq lengthEq)
  have secondProjection :
      (prefixes.zip queries).map Prod.snd = queries :=
    List.map_snd_zip (le_of_eq lengthEq.symm)
  have pairedOrdinary :
      ∀ entry ∈ prefixes.zip queries,
        entry.2.kind = .ordinary := by
    intro entry entryMember
    apply ordinary entry.2
    have member : entry.2 ∈ (prefixes.zip queries).map Prod.snd :=
      List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    simpa only [secondProjection] using member
  have pairedPositive :
      ∀ entry ∈ prefixes.zip queries,
        0 < entry.2.rawLength := by
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
    (prefixes.zip queries) pairedOrdinary pairedPositive
  rw [prefixProjection, secondProjection] at joined
  exact joined

end NormalizedFallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
