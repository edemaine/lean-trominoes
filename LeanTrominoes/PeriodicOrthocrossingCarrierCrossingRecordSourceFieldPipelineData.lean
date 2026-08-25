/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairSelectorData
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresencePipelineData
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamData

/-! # Physical pipeline for source-key crossing-record fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceFieldPipeline

def selectedCrossingTokens
    (field : CarrierCrossingRecordSourceField.Field)
    (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  DelimitedBinaryWordPairSelector.tokens
    (CarrierCrossingRecordSourceField.component field)
    (CarrierSourceKeyComponentStream.crossingTokens input)

def crossingFields
    (field : CarrierCrossingRecordSourceField.Field)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  CarrierKeyFieldProjector.output
    (CarrierCrossingRecordSourceField.keyField field)
    (selectedCrossingTokens field input)

/-- Terminal zero fields precede crossing fields; the crossing projector's
finish output supplies the single final lookup sentinel. -/
def fields (field : CarrierCrossingRecordSourceField.Field)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  CarrierBoundaryPresencePipeline.terminalFields input ++
    crossingFields field input

end CarrierCrossingRecordSourceFieldPipeline
end LeanTrominoes.PeriodicOrthocrossing
