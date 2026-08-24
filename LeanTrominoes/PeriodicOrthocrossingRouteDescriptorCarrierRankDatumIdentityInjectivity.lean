/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumData

/-! # Identity injectivity on route-descriptor rank data -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The reversible identity field is injective on rank data obtained from the
retained physical carrier-node stream. -/
theorem carrierRankDatumIdentity_injectiveOn_routeDescriptorRankDatums
    (period : Nat) (descriptors : List RouteDescriptor) :
    ∀ first ∈ routeDescriptorCarrierRankDatumsAtPeriod period descriptors,
      ∀ second ∈ routeDescriptorCarrierRankDatumsAtPeriod period descriptors,
        first.identity = second.identity → first = second := by
  intro first firstMember second secondMember identityEqual
  rcases List.mem_map.mp firstMember with
    ⟨firstNode, _firstNodeMember, rfl⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondNode, _secondNodeMember, rfl⟩
  change CarrierNode.code firstNode = CarrierNode.code secondNode at identityEqual
  exact congrArg (carrierNodeRankDatumAtPeriod period)
    (CarrierNode.code_injective identityEqual)

end LeanTrominoes.PeriodicOrthocrossing
