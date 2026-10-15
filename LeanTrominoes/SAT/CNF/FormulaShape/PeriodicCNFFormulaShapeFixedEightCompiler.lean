/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeFixedEightData
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFIndexedTemplateEmitterTime
import LeanTrominoes.Computation.TM2.TM2CompositionMachine
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time fixed-eight formula shapes -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FormulaShapeFixedEight

noncomputable def generatedShapeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List FormulaShape.Token) (List FormulaShape.Token)
      FormulaShape.Token FormulaShape.Token id id generatedShape := by
  let generated := TM2CompositionMachine.computableInPolyTime
    (IndexedTemplateEmitterMachine.computableInPolyTime family)
    (FiniteBlockTransducer.computableInPolyTime decodeItem)
  exact generated

noncomputable def shapeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List FormulaShape.Token) (List FormulaShape.Token)
      FormulaShape.Token FormulaShape.Token id id shape :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    generatedShapeComputableInPolyTime generatedShape_eq

end FormulaShapeFixedEight
end PeriodicCNF
end LeanTrominoes
