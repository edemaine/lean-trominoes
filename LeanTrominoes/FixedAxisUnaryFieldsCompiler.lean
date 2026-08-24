/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFields
import LeanTrominoes.TM2CompositionMachine

/-! # Composing fixed-axis unary fields after an activation compiler -/

noncomputable section

namespace LeanTrominoes.FixedAxisUnaryFields

open Computability Turing

/-- Any polynomial-time activation generator can be followed by the fixed
axis-to-unary adapter without changing its input boundary. -/
noncomputable def afterComputableInPolyTime
    {Input InputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (axes : List Bool) (activations : Input → List Bool)
    (activationCompiler :
      TM2ComputableInPolyTime encodeInput id activations) :
    TM2ComputableInPolyTime encodeInput id
      (fun input => compiledFields axes (activations input)) :=
  TM2CompositionMachine.computableInPolyTime activationCompiler
    (compiledFieldsComputableInPolyTime axes)

end LeanTrominoes.FixedAxisUnaryFields

end
