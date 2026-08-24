/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeSourceKeyInjectivity

/-! # Compact source-key equality on retained carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- On retained route-descriptor carrier nodes, compact source-key equality
is exactly equality of the reversible numeric node codes. -/
theorem sourceKeyPair_eq_iff_code_eq_of_mem_retainedCarrierNodes
    (period : Nat) (descriptors : List RouteDescriptor)
    (first second : CarrierNode)
    (firstMember : first ∈
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors)
    (secondMember : second ∈
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors) :
    CarrierNodeSourceKeys.pair first = CarrierNodeSourceKeys.pair second ↔
      CarrierNode.code first = CarrierNode.code second := by
  constructor
  · intro sourceKeyEqual
    exact congrArg CarrierNode.code
      (sourceKeyPair_injectiveOn_routeDescriptorRetainedCarrierNodesAtPeriod
        period descriptors first firstMember second secondMember
        sourceKeyEqual)
  · intro codeEqual
    exact congrArg CarrierNodeSourceKeys.pair
      (CarrierNode.code_injective codeEqual)

end LeanTrominoes.PeriodicOrthocrossing
