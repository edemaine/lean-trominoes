/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupData

/-! # Representative lookup for indexed crossing-segment fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingIndexedSegmentField

def values (field : Field) (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyRepresentativeLookup.values
    (CarrierCrossingIndexedSegmentCandidateFieldStream.valuesWithSentinel field)
    descriptors

end CarrierCrossingIndexedSegmentField
end LeanTrominoes.PeriodicOrthocrossing
