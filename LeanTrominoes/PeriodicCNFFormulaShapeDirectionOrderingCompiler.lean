/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingData
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time finite direction-aware shape ordering -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FormulaShapeDirectionOrdering

/-- Sorting a width-three direction-annotated profile is a fixed finite
lookup, so the complete annotated shape is a finite block transduction. -/
noncomputable def shapeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List FormulaShape.Token)
      Token FormulaShape.Token id id shape :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

/-- Any polynomial-time producer of finite direction descriptors composes
directly with the fixed clockwise lookup. -/
noncomputable def shapeComputableInPolyTimeOf
    {Source InputSymbol : Type}
    (encodeInput : Source → List InputSymbol)
    (descriptors : Source → List Token)
    (compiler : @TM2ComputableInPolyTime
      Source (List Token) InputSymbol Token
      encodeInput id descriptors) :
    @TM2ComputableInPolyTime
      Source (List FormulaShape.Token)
      InputSymbol FormulaShape.Token encodeInput id
      (fun input => shape (descriptors input)) :=
  TM2CompositionMachine.computableInPolyTime compiler
    shapeComputableInPolyTime

end FormulaShapeDirectionOrdering
end PeriodicCNF
end LeanTrominoes
