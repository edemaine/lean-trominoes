/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceShapeData
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time occurrence-split formula shapes -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace ClauseProfileOccurrenceShape

open UnaryProgramClauseProfile

noncomputable def generatedShapeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List ClauseProfile) (List FormulaShape.Token)
      ClauseProfile FormulaShape.Token id id generatedShape := by
  let generated := TM2CompositionMachine.computableInPolyTime
    (IndexedTemplateEmitterMachine.computableInPolyTime family)
    (FiniteBlockTransducer.computableInPolyTime decodeItem)
  exact generated

noncomputable def shapeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List ClauseProfile) (List FormulaShape.Token)
      ClauseProfile FormulaShape.Token id id shape :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    generatedShapeComputableInPolyTime generatedShape_eq

end ClauseProfileOccurrenceShape
end PeriodicCNF
end LeanTrominoes
