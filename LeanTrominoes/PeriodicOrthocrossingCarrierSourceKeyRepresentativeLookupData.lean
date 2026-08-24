/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupMachine
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierSourceKeyCandidateStreamData

/-! # Generic lookup through compact carrier representatives -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRepresentativeLookup

/-- Apply every compact source-key representative row to an arbitrary aligned
unary value stream. -/
def values (alignedValues : List RouteDescriptor → List Nat)
    (descriptors : List RouteDescriptor) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (paddedCarrierSourceKeyRepresentativeRows descriptors).words
    (alignedValues descriptors)

end CarrierSourceKeyRepresentativeLookup
end LeanTrominoes.PeriodicOrthocrossing
