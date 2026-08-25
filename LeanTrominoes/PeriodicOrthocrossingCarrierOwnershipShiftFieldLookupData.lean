/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupData

/-! # Representative lookup for carrier ownership-shift fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOwnershipShiftField

def values (field : Field) (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyRepresentativeLookup.values
    (CarrierOwnershipShiftCandidateFieldStream.valuesWithSentinel field)
    descriptors

end CarrierOwnershipShiftField
end LeanTrominoes.PeriodicOrthocrossing
