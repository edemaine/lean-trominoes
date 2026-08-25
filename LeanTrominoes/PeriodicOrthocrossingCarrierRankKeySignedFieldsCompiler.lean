/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorSignedWordCorrect
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeySignedFieldsData

/-! # Compilers for signed-coordinate carrier-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeySignedFields

open Computability Turing

noncomputable def horizontalPositiveValuesComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields horizontalPositiveValues :=
  CarrierRankKeyField.valuesComputableInPolyTime .horizontalPositive
    CarrierKeyFieldProjector.wordCorrect_horizontalPositive

noncomputable def horizontalNegativeValuesComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields horizontalNegativeValues :=
  CarrierRankKeyField.valuesComputableInPolyTime .horizontalNegative
    CarrierKeyFieldProjector.wordCorrect_horizontalNegative

noncomputable def verticalPositiveValuesComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields verticalPositiveValues :=
  CarrierRankKeyField.valuesComputableInPolyTime .verticalPositive
    CarrierKeyFieldProjector.wordCorrect_verticalPositive

noncomputable def verticalNegativeValuesComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields verticalNegativeValues :=
  CarrierRankKeyField.valuesComputableInPolyTime .verticalNegative
    CarrierKeyFieldProjector.wordCorrect_verticalNegative

end CarrierRankKeySignedFields
end LeanTrominoes.PeriodicOrthocrossing

end
