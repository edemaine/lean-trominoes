/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldCompiler

/-! # Compiler for carrier rank-scan fields forty-two through forty-nine -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

open Computability Turing

noncomputable def encodedSuffixComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding id encodedSuffix := by
  let c49 := singletonComputableInPolyTime .ownershipVerticalNegative
    (CarrierOwnershipShiftField.valuesComputableInPolyTime .verticalNegative)
  let c48 := prependComputableInPolyTime .ownershipVerticalPositive
    (CarrierOwnershipShiftField.valuesComputableInPolyTime .verticalPositive)
    c49
  let c47 := prependComputableInPolyTime .ownershipHorizontalNegative
    (CarrierOwnershipShiftField.valuesComputableInPolyTime
      .horizontalNegative) c48
  let c46 := prependComputableInPolyTime .ownershipHorizontalPositive
    (CarrierOwnershipShiftField.valuesComputableInPolyTime
      .horizontalPositive) c47
  let c45 := prependComputableInPolyTime .crossingPointVerticalNegative
    (CarrierCrossingPointField.valuesComputableInPolyTime .verticalNegative)
    c46
  let c44 := prependComputableInPolyTime .crossingPointVerticalPositive
    (CarrierCrossingPointField.valuesComputableInPolyTime .verticalPositive)
    c45
  let c43 := prependComputableInPolyTime .crossingPointHorizontalNegative
    (CarrierCrossingPointField.valuesComputableInPolyTime
      .horizontalNegative) c44
  let c42 := prependComputableInPolyTime .crossingPointHorizontalPositive
    (CarrierCrossingPointField.valuesComputableInPolyTime
      .horizontalPositive) c43
  unfold encodedSuffix suffixFields
  exact c42

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing

end
