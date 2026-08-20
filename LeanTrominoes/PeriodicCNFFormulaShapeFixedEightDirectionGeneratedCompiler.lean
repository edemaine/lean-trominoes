/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionGeneratedSemantics
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time exact fixed-eight direction descriptors -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FormulaShapeFixedEightDirection

/-- Both retained-input phases followed by the fixed finite decoder run in
polynomial time. -/
noncomputable def generatedDescriptorsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List FormulaShapeDirectionOrdering.Token)
      (List FormulaShapeDirectionOrdering.Token)
      FormulaShapeDirectionOrdering.Token
      FormulaShapeDirectionOrdering.Token
      id id generatedDescriptors := by
  let cyclePass :=
    IndexedTemplateEmitterMachine.computableInPolyTime cycleFamily
  let variablePass :=
    IndexedTemplateEmitterMachine.computableInPolyTime variableFamily
  let bothPasses :=
    TM2CompositionMachine.computableInPolyTime cyclePass variablePass
  let decoded := TM2CompositionMachine.computableInPolyTime bothPasses
    (FiniteBlockTransducer.computableInPolyTime decodeGeneratedItem)
  unfold generatedDescriptors
  exact decoded

/-- The exact canonical phase-major fixed-eight direction expansion is
polynomial-time computable. -/
noncomputable def descriptorsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List FormulaShapeDirectionOrdering.Token)
      (List FormulaShapeDirectionOrdering.Token)
      FormulaShapeDirectionOrdering.Token
      FormulaShapeDirectionOrdering.Token
      id id descriptors :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    generatedDescriptorsComputableInPolyTime generatedDescriptors_eq

/-- Any polynomial-time producer of pre-split direction descriptors composes
with the exact fixed-eight phase expansion. -/
noncomputable def descriptorsComputableInPolyTimeOf
    {Source InputSymbol : Type}
    (encodeInput : Source → List InputSymbol)
    (sourceDescriptors : Source →
      List FormulaShapeDirectionOrdering.Token)
    (compiler : @TM2ComputableInPolyTime
      Source (List FormulaShapeDirectionOrdering.Token)
      InputSymbol FormulaShapeDirectionOrdering.Token
      encodeInput id sourceDescriptors) :
    @TM2ComputableInPolyTime
      Source (List FormulaShapeDirectionOrdering.Token)
      InputSymbol FormulaShapeDirectionOrdering.Token
      encodeInput id
      (fun input => descriptors (sourceDescriptors input)) :=
  TM2CompositionMachine.computableInPolyTime compiler
    descriptorsComputableInPolyTime

end FormulaShapeFixedEightDirection
end PeriodicCNF
end LeanTrominoes
