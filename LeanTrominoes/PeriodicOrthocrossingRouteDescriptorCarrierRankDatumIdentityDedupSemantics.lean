/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupMapInjectiveOn
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumIdentityInjectivity

/-! # Rank-datum reconstruction from deduplicated identities -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Deduplicating reversible identities and reconstructing their rank data is
exactly stable deduplication of the original route-descriptor rank data. -/
theorem dedup_rankDatumIdentities_map_reconstruct_field
    (period : Nat) (descriptors : List RouteDescriptor)
    (field : CarrierNodeRankDatum → Nat) :
    ((routeDescriptorCarrierRankDatumsAtPeriod period descriptors).map
        CarrierNodeRankDatum.identity).dedup.map (fun code =>
          field (carrierNodeRankDatumAtPeriod period code.node)) =
      (routeDescriptorCarrierRankDatumsAtPeriod
        period descriptors).dedup.map field := by
  rw [List.dedup_map_of_injective_on
    CarrierNodeRankDatum.identity
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors)
    (carrierRankDatumIdentity_injectiveOn_routeDescriptorRankDatums
      period descriptors)]
  rw [List.map_map]
  apply List.map_congr_left
  intro datum datumMember
  rcases List.mem_map.mp (List.mem_dedup.mp datumMember) with
    ⟨node, _nodeMember, rfl⟩
  simp [Function.comp_apply, carrierNodeRankDatumAtPeriod]

end LeanTrominoes.PeriodicOrthocrossing
