import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseOrbits

/-!
# Degree bounds for retained carrier representatives

The retained carrier construction selects one physical representative from
each periodic link orbit.  To bound occurrences after periodic
normalization, we first record the directed-chain uniqueness facts at both
ends of every retained carrier link.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- In a duplicate-free chain, an adjacent pair is determined by its second
entry. -/
theorem consecutivePairs_eq_of_snd_eq_of_nodup
    {Value : Type*}
    {values : List Value}
    (nodup : values.Nodup)
    {first second : Value × Value}
    (firstMem : first ∈ consecutivePairs values)
    (secondMem : second ∈ consecutivePairs values)
    (sndEq : first.2 = second.2) :
    first = second := by
  have secondEndpointsNodup :
      ((consecutivePairs values).map Prod.snd).Nodup :=
    nodup.sublist (consecutivePairs_snd_sublist values)
  exact List.inj_on_of_nodup_map secondEndpointsNodup
    firstMem secondMem sndEq

/-- A raw retained carrier link is determined by its physical second
endpoint. -/
theorem retainedDrawingCompleteCarrierLinksRaw_eq_of_second_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {first second : EqualityLink CarrierNode}
    (firstMem :
      first ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (secondMem :
      second ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (secondEq : first.second = second.second) :
    first = second := by
  rcases List.mem_flatMap.mp firstMem with
    ⟨firstKey, _firstKeyMem, firstChainMem⟩
  rcases List.mem_flatMap.mp secondMem with
    ⟨secondKey, _secondKeyMem, secondChainMem⟩
  have firstCommon :=
    retainedCompleteCarrierLinks_common_key
      graph firstKey firstChainMem
  have secondCommon :=
    retainedCompleteCarrierLinks_common_key
      graph secondKey secondChainMem
  have keyEq : firstKey = secondKey := by
    rw [← firstCommon.2, ← secondCommon.2, secondEq]
  subst secondKey
  rcases List.mem_map.mp firstChainMem with
    ⟨firstPair, firstPairMem, firstLinkEq⟩
  rcases List.mem_map.mp secondChainMem with
    ⟨secondPair, secondPairMem, secondLinkEq⟩
  have pairEq :
      firstPair = secondPair := by
    apply consecutivePairs_eq_of_snd_eq_of_nodup
      (retainedCompleteCarrierNodes_nodup graph firstKey)
      (List.mem_filter.mp firstPairMem).1
      (List.mem_filter.mp secondPairMem).1
    calc
      firstPair.2 =
          first.second :=
        congrArg EqualityLink.second firstLinkEq
      _ = second.second := secondEq
      _ = secondPair.2 :=
        (congrArg EqualityLink.second secondLinkEq).symm
  subst secondPair
  exact firstLinkEq.symm.trans secondLinkEq

/-- A selected retained carrier link is determined by its physical second
endpoint. -/
theorem retainedDrawingCompleteCarrierLinks_eq_of_second_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {first second : EqualityLink CarrierNode}
    (firstMem :
      first ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem :
      second ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondEq : first.second = second.second) :
    first = second := by
  exact retainedDrawingCompleteCarrierLinksRaw_eq_of_second_eq
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph first).mp firstMem).1
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph second).mp secondMem).1
    secondEq

end PeriodicOrthocrossing
end LeanTrominoes
