/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldCompiler

/-! # Compiler for carrier rank-scan fields twenty-eight through forty-one -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

open Computability Turing

noncomputable def encodedSecondCrossingComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding id
      encodedSecondCrossing := by
  let c41 := singletonComputableInPolyTime
    .crossingSecondTranslateVerticalNegative
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime
      .secondTranslateVerticalNegative)
  let c40 := prependComputableInPolyTime
    .crossingSecondTranslateVerticalPositive
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime
      .secondTranslateVerticalPositive) c41
  let c39 := prependComputableInPolyTime
    .crossingSecondTranslateHorizontalNegative
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime
      .secondTranslateHorizontalNegative) c40
  let c38 := prependComputableInPolyTime
    .crossingSecondTranslateHorizontalPositive
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime
      .secondTranslateHorizontalPositive) c39
  let c37 := prependComputableInPolyTime
    .crossingSecondFinishVerticalNegative
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .second .finish false false)) c38
  let c36 := prependComputableInPolyTime
    .crossingSecondFinishVerticalPositive
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .second .finish false true)) c37
  let c35 := prependComputableInPolyTime
    .crossingSecondFinishHorizontalNegative
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .second .finish true false)) c36
  let c34 := prependComputableInPolyTime
    .crossingSecondFinishHorizontalPositive
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .second .finish true true)) c35
  let c33 := prependComputableInPolyTime
    .crossingSecondStartVerticalNegative
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .second .start false false)) c34
  let c32 := prependComputableInPolyTime
    .crossingSecondStartVerticalPositive
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .second .start false true)) c33
  let c31 := prependComputableInPolyTime
    .crossingSecondStartHorizontalNegative
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .second .start true false)) c32
  let c30 := prependComputableInPolyTime
    .crossingSecondStartHorizontalPositive
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .second .start true true)) c31
  let c29 := prependComputableInPolyTime .crossingSecondSegment
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime
      .secondSegment) c30
  let c28 := prependComputableInPolyTime .crossingSecondRoute
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime .secondRoute)
    c29
  unfold encodedSecondCrossing secondCrossingFields
  exact c28

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing

end
