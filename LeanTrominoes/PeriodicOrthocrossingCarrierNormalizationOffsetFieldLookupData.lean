/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupData

/-! # Representative lookup for carrier normalization-offset fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizationOffsetField

def values (field : Field) (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyRepresentativeLookup.values
    (CarrierNormalizationOffsetCandidateFieldStream.valuesWithSentinel field)
    descriptors

end CarrierNormalizationOffsetField
end LeanTrominoes.PeriodicOrthocrossing
