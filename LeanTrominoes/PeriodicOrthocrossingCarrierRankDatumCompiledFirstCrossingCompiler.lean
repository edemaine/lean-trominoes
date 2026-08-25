/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldCompiler

/-! # Compiler for carrier rank-scan fields fourteen through twenty-seven -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

open Computability Turing

noncomputable def encodedFirstCrossingComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding id
      encodedFirstCrossing := by
  let c27 := singletonComputableInPolyTime
    .crossingFirstTranslateVerticalNegative
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime
      .firstTranslateVerticalNegative)
  let c26 := prependComputableInPolyTime
    .crossingFirstTranslateVerticalPositive
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime
      .firstTranslateVerticalPositive) c27
  let c25 := prependComputableInPolyTime
    .crossingFirstTranslateHorizontalNegative
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime
      .firstTranslateHorizontalNegative) c26
  let c24 := prependComputableInPolyTime
    .crossingFirstTranslateHorizontalPositive
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime
      .firstTranslateHorizontalPositive) c25
  let c23 := prependComputableInPolyTime
    .crossingFirstFinishVerticalNegative
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .first .finish false false)) c24
  let c22 := prependComputableInPolyTime
    .crossingFirstFinishVerticalPositive
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .first .finish false true)) c23
  let c21 := prependComputableInPolyTime
    .crossingFirstFinishHorizontalNegative
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .first .finish true false)) c22
  let c20 := prependComputableInPolyTime
    .crossingFirstFinishHorizontalPositive
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .first .finish true true)) c21
  let c19 := prependComputableInPolyTime
    .crossingFirstStartVerticalNegative
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .first .start false false)) c20
  let c18 := prependComputableInPolyTime
    .crossingFirstStartVerticalPositive
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .first .start false true)) c19
  let c17 := prependComputableInPolyTime
    .crossingFirstStartHorizontalNegative
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .first .start true false)) c18
  let c16 := prependComputableInPolyTime
    .crossingFirstStartHorizontalPositive
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      (.coordinate .first .start true true)) c17
  let c15 := prependComputableInPolyTime .crossingFirstSegment
    (CarrierCrossingIndexedSegmentField.valuesComputableInPolyTime
      .firstSegmentIndex) c16
  let c14 := prependComputableInPolyTime .crossingFirstRoute
    (CarrierCrossingRecordSourceField.valuesComputableInPolyTime .firstRoute)
    c15
  unfold encodedFirstCrossing firstCrossingFields
  exact c14

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing

end
