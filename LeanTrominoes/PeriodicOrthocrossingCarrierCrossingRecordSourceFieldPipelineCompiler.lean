/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairSelectorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresencePipelineCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldPipelineData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamCompiler

/-! # Compiler for source-key crossing-record field pipelines -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceFieldPipeline

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

noncomputable def selectedCrossingTokensComputableInPolyTime
    (field : CarrierCrossingRecordSourceField.Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (selectedCrossingTokens field) := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input =>
      DelimitedBinaryWordPairSelector.tokens
        (CarrierCrossingRecordSourceField.component field)
        (CarrierSourceKeyComponentStream.crossingTokens input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierSourceKeyComponentStream.crossingTokensComputableInPolyTime
    (DelimitedBinaryWordPairSelector.tokensComputableInPolyTime
      (CarrierCrossingRecordSourceField.component field))

noncomputable def crossingFieldsComputableInPolyTime
    (field : CarrierCrossingRecordSourceField.Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (crossingFields field) := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input =>
      CarrierKeyFieldProjector.output
        (CarrierCrossingRecordSourceField.keyField field)
        (selectedCrossingTokens field input))
  exact TM2CompositionMachine.computableInPolyTime
    (selectedCrossingTokensComputableInPolyTime field)
    (CarrierKeyFieldProjector.computableInPolyTime
      (CarrierCrossingRecordSourceField.keyField field))

noncomputable def fieldsComputableInPolyTime
    (field : CarrierCrossingRecordSourceField.Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (fields field) := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input =>
      CarrierBoundaryPresencePipeline.terminalFields input ++
        crossingFields field input)
  exact TM2ListAppend.computableInPolyTime
    CarrierBoundaryPresencePipeline.terminalFieldsComputableInPolyTime
    (crossingFieldsComputableInPolyTime field)

end CarrierCrossingRecordSourceFieldPipeline
end LeanTrominoes.PeriodicOrthocrossing

end
