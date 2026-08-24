/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupTime
import LeanTrominoes.TM2CompositionMachine

/-! # Composition interface for last-true unary lookup -/

noncomputable section

namespace LeanTrominoes.LastTrueUnaryValueLookupMachine

open Computability Turing

/-- Any polynomial-time compiler for promised lookup inputs can be followed
by the verified quadratic lookup machine. -/
noncomputable def afterComputableInPolyTime
    {Source SourceSymbol : Type}
    [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol)
    (makeInput : Source → Input)
    (inputComputableInPolyTime :
      @TM2ComputableInPolyTime
        Source Input SourceSymbol InputSymbol
        encodeSource encode makeInput) :
    @TM2ComputableInPolyTime
      Source (List Nat) SourceSymbol UnarySymbol
      encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun source => lookups (makeInput source).rows
        (makeInput source).values) :=
  TM2CompositionMachine.computableInPolyTime
    inputComputableInPolyTime computableInPolyTime

end LeanTrominoes.LastTrueUnaryValueLookupMachine

end
