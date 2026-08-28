/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeFixedFieldLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRepresentativeFieldLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateSupport

/-! # Fixed-width lookup of normalized fields by carrier identity -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRepresentativeFieldLookup

open PaddedSupportedLastRepresentativeEqualityRows

/-- Specialize fixed-width representative lookup to the normalized field
block aligned with each reversible carrier identity. -/
noncomputable def identityFieldLookups :=
  fun period descriptors =>
    lookups_fixedFieldRows_selfSupported
      (paddedCarrierIdentityCandidateStreamAtPeriod period descriptors)
      (paddedCarrierIdentityCandidateStream_supported_eq_isSome
        period descriptors)
      (identityFieldsAtPeriod period)
      CarrierSourceKeyRepresentativeFieldLookup.fieldCount
      (identityFieldsAtPeriod_length period)

end CarrierNormalizedSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing

end
