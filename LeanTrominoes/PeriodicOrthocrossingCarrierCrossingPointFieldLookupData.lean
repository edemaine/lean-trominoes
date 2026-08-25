/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupData

/-! # Representative lookup for crossing-point fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingPointField

def values (field : Field) (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyRepresentativeLookup.values
    (CarrierCrossingPointCandidateFieldStream.valuesWithSentinel field)
    descriptors

end CarrierCrossingPointField
end LeanTrominoes.PeriodicOrthocrossing
