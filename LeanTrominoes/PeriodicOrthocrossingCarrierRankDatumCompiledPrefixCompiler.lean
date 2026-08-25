/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankHorizontalFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRouteFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeySegmentFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeySignedFieldsCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldCompiler

/-! # Compiler for carrier rank-scan fields zero through thirteen -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

open Computability Turing

noncomputable def encodedPrefixComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding id encodedPrefix := by
  let c13 := singletonComputableInPolyTime .boundaryPresence
    CarrierBoundaryPresenceField.valuesComputableInPolyTime
  let c12 := prependComputableInPolyTime .normalizationVerticalNegative
    (CarrierNormalizationOffsetField.valuesComputableInPolyTime
      .verticalNegative) c13
  let c11 := prependComputableInPolyTime .normalizationVerticalPositive
    (CarrierNormalizationOffsetField.valuesComputableInPolyTime
      .verticalPositive) c12
  let c10 := prependComputableInPolyTime .normalizationHorizontalNegative
    (CarrierNormalizationOffsetField.valuesComputableInPolyTime
      .horizontalNegative) c11
  let c9 := prependComputableInPolyTime .normalizationHorizontalPositive
    (CarrierNormalizationOffsetField.valuesComputableInPolyTime
      .horizontalPositive) c10
  let c8 := prependComputableInPolyTime .horizontal
    CarrierRankHorizontalField.valuesComputableInPolyTime c9
  let c7 := prependComputableInPolyTime .orderNegative
    (CarrierRankOrderField.valuesComputableInPolyTime false) c8
  let c6 := prependComputableInPolyTime .orderPositive
    (CarrierRankOrderField.valuesComputableInPolyTime true) c7
  let c5 := prependComputableInPolyTime .keyTranslateVerticalNegative
    CarrierRankKeySignedFields.verticalNegativeValuesComputableInPolyTime c6
  let c4 := prependComputableInPolyTime .keyTranslateVerticalPositive
    CarrierRankKeySignedFields.verticalPositiveValuesComputableInPolyTime c5
  let c3 := prependComputableInPolyTime .keyTranslateHorizontalNegative
    CarrierRankKeySignedFields.horizontalNegativeValuesComputableInPolyTime c4
  let c2 := prependComputableInPolyTime .keyTranslateHorizontalPositive
    CarrierRankKeySignedFields.horizontalPositiveValuesComputableInPolyTime c3
  let c1 := prependComputableInPolyTime .keySegment
    CarrierRankKeySegmentField.valuesComputableInPolyTime c2
  let c0 := prependComputableInPolyTime .keyRoute
    CarrierRankKeyRouteField.valuesComputableInPolyTime c1
  unfold encodedPrefix prefixFields
  exact c0

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing

end
