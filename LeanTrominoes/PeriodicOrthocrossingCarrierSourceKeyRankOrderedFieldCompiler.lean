/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRankOrderedFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeFieldLookupCompiler
import LeanTrominoes.UnaryPermutationRankBlockLookupCompiler

/-! # Compiler for carrier source-key fields in global rank order -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRankOrderedFields

open Computability Turing

abbrev descriptorInputEncoding :
    List RouteDescriptor → List DelimitedBinaryWords.Token :=
  CarrierSourceKeyRepresentativeFieldLookup.descriptorInputEncoding

/-- All twelve physical source-key fields of every retained carrier identity
are emitted together in global carrier-rank order in polynomial time. -/
noncomputable def valuesComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding
      UnaryFieldEncoderMachine.unaryFields values := by
  exact UnaryPermutationRankBlockLookup.valuesComputableInPolyTime
    descriptorInputEncoding fieldCount CarrierRankGlobal.ranks
    CarrierSourceKeyRepresentativeFieldLookup.selectedFields
    selectedFields_length
    CarrierRankGlobal.ranksComputableInPolyTime
    CarrierSourceKeyRepresentativeFieldLookup.selectedFieldsComputableInPolyTime

end CarrierSourceKeyRankOrderedFields
end LeanTrominoes.PeriodicOrthocrossing

end
